// Copyright 2014 Collabora Ltd. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "content/renderer/media/gstreamer/webmediaplayer_gst.h"

#include <algorithm>
#include <limits>
#include <string>
#include <vector>

#include "base/bind.h"
#include "base/callback.h"
#include "base/callback_helpers.h"
#include "base/command_line.h"
#include "base/debug/alias.h"
#include "base/debug/crash_logging.h"
#include "base/debug/trace_event.h"
#include "base/message_loop/message_loop_proxy.h"
#include "base/metrics/histogram.h"
#include "base/strings/string_number_conversions.h"
#include "base/strings/utf_string_conversions.h"
#include "base/synchronization/waitable_event.h"
#include "cc/layers/video_layer.h"
#include "content/public/common/content_switches.h"
#include "content/public/renderer/render_frame.h"
#include "content/renderer/media/buffered_data_source.h"
#include "content/renderer/media/crypto/key_systems.h"
#include "content/renderer/media/render_media_log.h"
#include "content/renderer/media/texttrack_impl.h"
#include "content/renderer/media/webaudiosourceprovider_impl.h"
#include "content/renderer/media/webinbandtexttrack_impl.h"
#include "content/renderer/media/webmediaplayer_delegate.h"
#include "content/renderer/media/webmediaplayer_params.h"
#include "content/renderer/media/webmediaplayer_util.h"
#include "content/renderer/media/webmediasource_impl.h"
#include "content/renderer/pepper/pepper_webplugin_impl.h"
#include "content/renderer/render_thread_impl.h"
#include "gpu/GLES2/gl2extchromium.h"
#include "gpu/command_buffer/common/mailbox_holder.h"
#include "media/audio/null_audio_sink.h"
#include "media/base/audio_hardware_config.h"
#include "media/base/bind_to_current_loop.h"
#include "media/base/filter_collection.h"
#include "media/base/limits.h"
#include "media/base/media_log.h"
#include "media/base/media_switches.h"
#include "media/base/pipeline.h"
#include "media/base/text_renderer.h"
#include "media/base/text_track_config.h"
#include "media/base/video_frame.h"
#include "third_party/WebKit/public/platform/WebContentDecryptionModule.h"
#include "third_party/WebKit/public/platform/WebMediaSource.h"
#include "third_party/WebKit/public/platform/WebRect.h"
#include "third_party/WebKit/public/platform/WebSize.h"
#include "third_party/WebKit/public/platform/WebString.h"
#include "third_party/WebKit/public/platform/WebURL.h"
#include "third_party/WebKit/public/web/WebDocument.h"
#include "third_party/WebKit/public/web/WebLocalFrame.h"
#include "third_party/WebKit/public/web/WebRuntimeFeatures.h"
#include "third_party/WebKit/public/web/WebSecurityOrigin.h"
#include "third_party/WebKit/public/web/WebView.h"
#include "v8/include/v8.h"
#include "webkit/renderer/compositor_bindings/web_layer_impl.h"

using blink::WebCanvas;
using blink::WebMediaPlayer;
using blink::WebRect;
using blink::WebSize;
using blink::WebString;

namespace {

// Amount of extra memory used by each player instance reported to V8.
// It is not exact number -- first, it differs on different platforms,
// and second, it is very hard to calculate. Instead, use some arbitrary
// value that will cause garbage collection from time to time. We don't want
// it to happen on every allocation, but don't want 5k players to sit in memory
// either. Looks that chosen constant achieves both goals, at least for audio
// objects. (Do not worry about video objects yet, JS programs do not create
// thousands of them...)
// TODO: remove me
const int kPlayerExtraMemory = 1024 * 1024;

// Limits the range of playback rate.
//
// TODO(kylep): Revisit these.
//
// Vista has substantially lower performance than XP or Windows7.  If you speed
// up a video too much, it can't keep up, and rendering stops updating except on
// the time bar. For really high speeds, audio becomes a bottleneck and we just
// use up the data we have, which may not achieve the speed requested, but will
// not crash the tab.
//
// A very slow speed, ie 0.00000001x, causes the machine to lock up. (It seems
// like a busy loop). It gets unresponsive, although its not completely dead.
//
// Also our timers are not very accurate (especially for ogg), which becomes
// evident at low speeds and on Vista. Since other speeds are risky and outside
// the norms, we think 1/16x to 16x is a safe and useful range for now.
const double kMinRate = 0.0625;
const double kMaxRate = 16.0;

}  // namespace

namespace content {

class BufferedDataSourceHostImpl;

#define COMPILE_ASSERT_MATCHING_ENUM(name) \
  COMPILE_ASSERT(static_cast<int>(WebMediaPlayer::CORSMode ## name) == \
                 static_cast<int>(BufferedResourceLoader::k ## name), \
                 mismatching_enums)
COMPILE_ASSERT_MATCHING_ENUM(Unspecified);
COMPILE_ASSERT_MATCHING_ENUM(Anonymous);
COMPILE_ASSERT_MATCHING_ENUM(UseCredentials);
#undef COMPILE_ASSERT_MATCHING_ENUM

#define BIND_TO_RENDER_LOOP(function) \
  (DCHECK(main_loop_->BelongsToCurrentThread()), \
  media::BindToCurrentLoop(base::Bind(function, AsWeakPtr())))

static void LogMediaSourceError(const scoped_refptr<media::MediaLog>& media_log,
                                const std::string& error) {
  media_log->AddEvent(media_log->CreateMediaSourceErrorEvent(error));
}

WebMediaPlayerGst::WebMediaPlayerGst(
    blink::WebLocalFrame* frame,
    blink::WebMediaPlayerClient* client,
    base::WeakPtr<WebMediaPlayerDelegate> delegate,
    const WebMediaPlayerParams& params)
    : frame_(frame),
      network_state_(WebMediaPlayer::NetworkStateEmpty),
      ready_state_(WebMediaPlayer::ReadyStateHaveNothing),
      main_loop_(base::MessageLoopProxy::current()),
      media_loop_(
          RenderThreadImpl::current()->GetMediaThreadMessageLoopProxy()),
      media_log_(new RenderMediaLog()),
      opaque_(false),
      paused_(true),
      seeking_(false),
      playback_rate_(0.0f),
      pending_seek_(false),
      pending_seek_seconds_(0.0f),
      client_(client),
      delegate_(delegate),
      defer_load_cb_(params.defer_load_cb()),
      accelerated_compositing_reported_(false),
      incremented_externally_allocated_memory_(false),
      is_local_source_(false),
      supports_save_(true),
      starting_(false),
      // Threaded compositing isn't enabled universally yet.
      compositor_task_runner_(
          RenderThreadImpl::current()->compositor_message_loop_proxy()
              ? RenderThreadImpl::current()->compositor_message_loop_proxy()
              : base::MessageLoopProxy::current()),
      compositor_(new VideoFrameCompositor(
          BIND_TO_RENDER_LOOP(&WebMediaPlayerGst::OnNaturalSizeChanged),
          BIND_TO_RENDER_LOOP(&WebMediaPlayerGst::OnOpacityChanged))),
      text_track_index_(0) {
  media_log_->AddEvent(
      media_log_->CreateEvent(media::MediaLogEvent::WEBMEDIAPLAYER_CREATED));

  // Let V8 know we started new thread if we did not do it yet.
  // Made separate task to avoid deletion of player currently being created.
  // Also, delaying GC until after player starts gets rid of starting lag --
  // collection happens in parallel with playing.
  //
  // TODO(enal): remove when we get rid of per-audio-stream thread.
  main_loop_->PostTask(
      FROM_HERE,
      base::Bind(&WebMediaPlayerGst::IncrementExternallyAllocatedMemory,
                 AsWeakPtr()));
}

WebMediaPlayerGst::~WebMediaPlayerGst() {
  client_->setWebLayer(NULL);

  DCHECK(main_loop_->BelongsToCurrentThread());
  media_log_->AddEvent(
      media_log_->CreateEvent(media::MediaLogEvent::WEBMEDIAPLAYER_DESTROYED));

  if (delegate_.get())
    delegate_->PlayerGone(this);

  // Abort any pending IO so stopping the pipeline doesn't get blocked.
  if (data_source_)
    data_source_->Abort();

  // FIXME: Make sure to kill the pipeline so there's no more media threads running.
  // Note: stopping the pipeline might block for a long time.

  compositor_task_runner_->DeleteSoon(FROM_HERE, compositor_);

  // Let V8 know we are not using extra resources anymore.
  if (incremented_externally_allocated_memory_) {
    v8::Isolate::GetCurrent()->AdjustAmountOfExternalAllocatedMemory(
        -kPlayerExtraMemory);
    incremented_externally_allocated_memory_ = false;
  }
}

namespace {

// Helper enum for reporting scheme histograms.
enum URLSchemeForHistogram {
  kUnknownURLScheme,
  kMissingURLScheme,
  kHttpURLScheme,
  kHttpsURLScheme,
  kFtpURLScheme,
  kChromeExtensionURLScheme,
  kJavascriptURLScheme,
  kFileURLScheme,
  kBlobURLScheme,
  kDataURLScheme,
  kFileSystemScheme,
  kMaxURLScheme = kFileSystemScheme  // Must be equal to highest enum value.
};

URLSchemeForHistogram URLScheme(const GURL& url) {
  if (!url.has_scheme()) return kMissingURLScheme;
  if (url.SchemeIs("http")) return kHttpURLScheme;
  if (url.SchemeIs("https")) return kHttpsURLScheme;
  if (url.SchemeIs("ftp")) return kFtpURLScheme;
  if (url.SchemeIs("chrome-extension")) return kChromeExtensionURLScheme;
  if (url.SchemeIs("javascript")) return kJavascriptURLScheme;
  if (url.SchemeIs("file")) return kFileURLScheme;
  if (url.SchemeIs("blob")) return kBlobURLScheme;
  if (url.SchemeIs("data")) return kDataURLScheme;
  if (url.SchemeIs("filesystem")) return kFileSystemScheme;
  return kUnknownURLScheme;
}

}  // namespace

void WebMediaPlayerGst::load(LoadType load_type, const blink::WebURL& url,
                             CORSMode cors_mode) {
  if (!defer_load_cb_.is_null()) {
    defer_load_cb_.Run(base::Bind(
        &WebMediaPlayerGst::DoLoad, AsWeakPtr(), load_type, url, cors_mode));
    return;
  }
  DoLoad(load_type, url, cors_mode);
}

void WebMediaPlayerGst::DoLoad(LoadType load_type,
                               const blink::WebURL& url,
                               CORSMode cors_mode) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  GURL gurl(url);
  UMA_HISTOGRAM_ENUMERATION("Media.URLScheme", URLScheme(gurl), kMaxURLScheme);

  // Set subresource URL for crash reporting.
  base::debug::SetCrashKeyValue("subresource_url", gurl.spec());

  load_type_ = load_type;

  // Handle any volume/preload changes that occurred before load().
  setVolume(client_->volume());
  setPreload(client_->preload());

  SetNetworkState(WebMediaPlayer::NetworkStateLoading);
  SetReadyState(WebMediaPlayer::ReadyStateHaveNothing);
  media_log_->AddEvent(media_log_->CreateLoadEvent(url.spec()));

  // Media source pipelines can start immediately.
  if (load_type == LoadTypeMediaSource) {
    supports_save_ = false;
    StartPipeline();
    return;
  }

  // Otherwise it's a regular request which requires resolving the URL first.
  data_source_.reset(new BufferedDataSource(
      main_loop_,
      frame_,
      media_log_.get(),
      &buffered_data_source_host_,
      base::Bind(&WebMediaPlayerGst::NotifyDownloading, AsWeakPtr())));
  data_source_->Initialize(
      url, static_cast<BufferedResourceLoader::CORSMode>(cors_mode),
      base::Bind(
          &WebMediaPlayerGst::DataSourceInitialized,
          AsWeakPtr(), gurl));

  is_local_source_ = !gurl.SchemeIsHTTPOrHTTPS();
}

void WebMediaPlayerGst::play() {
  DCHECK(main_loop_->BelongsToCurrentThread());

  paused_ = false;
  // FIXME
//  pipeline_.SetPlaybackRate(playback_rate_);
  if (data_source_)
    data_source_->MediaIsPlaying();

  media_log_->AddEvent(media_log_->CreateEvent(media::MediaLogEvent::PLAY));

  if (delegate_.get())
    delegate_->DidPlay(this);
}

void WebMediaPlayerGst::pause() {
  DCHECK(main_loop_->BelongsToCurrentThread());

  paused_ = true;
  // FIXME: grab time from pipeline and pause it
  if (data_source_)
    data_source_->MediaIsPaused();
//  paused_time_ = pipeline_.GetMediaTime();

  media_log_->AddEvent(media_log_->CreateEvent(media::MediaLogEvent::PAUSE));

  if (delegate_.get())
    delegate_->DidPause(this);
}

bool WebMediaPlayerGst::supportsSave() const {
  DCHECK(main_loop_->BelongsToCurrentThread());
  return supports_save_;
}

void WebMediaPlayerGst::seek(double seconds) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  if (ready_state_ > WebMediaPlayer::ReadyStateHaveMetadata)
    SetReadyState(WebMediaPlayer::ReadyStateHaveMetadata);

  base::TimeDelta seek_time = ConvertSecondsToTimestamp(seconds);

  if (starting_ || seeking_) {
    pending_seek_ = true;
    pending_seek_seconds_ = seconds;
    return;
  }

  media_log_->AddEvent(media_log_->CreateSeekEvent(seconds));

  // Update our paused time.
  if (paused_)
    paused_time_ = seek_time;

  seeking_ = true;

  // FIXME: Kick off the asynchronous seek!
}

void WebMediaPlayerGst::setRate(double rate) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // TODO(kylep): Remove when support for negatives is added. Also, modify the
  // following checks so rewind uses reasonable values also.
  if (rate < 0.0)
    return;

  // Limit rates to reasonable values by clamping.
  if (rate != 0.0) {
    if (rate < kMinRate)
      rate = kMinRate;
    else if (rate > kMaxRate)
      rate = kMaxRate;
  }

  playback_rate_ = rate;
  if (!paused_) {
    // FIXME: Set playback rate on pipeline
    if (data_source_)
      data_source_->MediaPlaybackRateChanged(rate);
  }
}

void WebMediaPlayerGst::setVolume(double volume) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME
}

#define COMPILE_ASSERT_MATCHING_ENUM(webkit_name, chromium_name) \
    COMPILE_ASSERT(static_cast<int>(WebMediaPlayer::webkit_name) == \
                   static_cast<int>(content::chromium_name), \
                   mismatching_enums)
COMPILE_ASSERT_MATCHING_ENUM(PreloadNone, NONE);
COMPILE_ASSERT_MATCHING_ENUM(PreloadMetaData, METADATA);
COMPILE_ASSERT_MATCHING_ENUM(PreloadAuto, AUTO);
#undef COMPILE_ASSERT_MATCHING_ENUM

void WebMediaPlayerGst::setPreload(WebMediaPlayer::Preload preload) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  if (data_source_)
    data_source_->SetPreload(static_cast<content::Preload>(preload));
}

bool WebMediaPlayerGst::hasVideo() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  return true;  // FIXME
}

bool WebMediaPlayerGst::hasAudio() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  return true;  // FIXME
}

blink::WebSize WebMediaPlayerGst::naturalSize() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  return WebSize (100, 100);  // FIXME
//  return blink::WebSize(pipeline_metadata_.natural_size);
}

bool WebMediaPlayerGst::paused() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  return false;  // FIXME
}

bool WebMediaPlayerGst::seeking() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  if (ready_state_ == WebMediaPlayer::ReadyStateHaveNothing)
    return false;

  return seeking_;
}

double WebMediaPlayerGst::duration() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  if (ready_state_ == WebMediaPlayer::ReadyStateHaveNothing)
    return std::numeric_limits<double>::quiet_NaN();

  base::TimeDelta duration = media::kInfiniteDuration();
  // FIXME: Get duration from pipeline

  // Return positive infinity if the resource is unbounded.
  // http://www.whatwg.org/specs/web-apps/current-work/multipage/video.html#dom-media-duration
  if (duration == media::kInfiniteDuration())
    return std::numeric_limits<double>::infinity();

  return duration.InSecondsF();
}

double WebMediaPlayerGst::timelineOffset() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  /*
  if (pipeline_metadata_.timeline_offset.is_null())
    return std::numeric_limits<double>::quiet_NaN();

  return pipeline_metadata_.timeline_offset.ToJsTime();
  */
  // FIXME
  return std::numeric_limits<double>::quiet_NaN();
}

double WebMediaPlayerGst::currentTime() const {
  DCHECK(main_loop_->BelongsToCurrentThread());
  // FIXME
  return paused_time_.InSecondsF();
//  return (paused_ ? paused_time_ : pipeline_.GetMediaTime()).InSecondsF();
}

WebMediaPlayer::NetworkState WebMediaPlayerGst::networkState() const {
  DCHECK(main_loop_->BelongsToCurrentThread());
  return network_state_;
}

WebMediaPlayer::ReadyState WebMediaPlayerGst::readyState() const {
  DCHECK(main_loop_->BelongsToCurrentThread());
  return ready_state_;
}

const blink::WebTimeRanges& WebMediaPlayerGst::buffered() {
  DCHECK(main_loop_->BelongsToCurrentThread());
/*  media::Ranges<base::TimeDelta> buffered_time_ranges =
      pipeline_.GetBufferedTimeRanges();
  buffered_data_source_host_.AddBufferedTimeRanges(
      &buffered_time_ranges, pipeline_.GetMediaDuration());
  blink::WebTimeRanges buffered_web_time_ranges(
      ConvertToWebTimeRanges(buffered_time_ranges));
  buffered_web_time_ranges_.swap(buffered_web_time_ranges);*/
  return buffered_web_time_ranges_;
  // FIXME
}

blink::WebTimeRanges WebMediaPlayerGst::buffered() const {
  DCHECK(main_loop_->BelongsToCurrentThread());
/*  media::Ranges<base::TimeDelta> buffered_time_ranges =
      pipeline_.GetBufferedTimeRanges();
  buffered_data_source_host_.AddBufferedTimeRanges(
      &buffered_time_ranges, pipeline_.GetMediaDuration());
  return ConvertToWebTimeRanges(buffered_time_ranges);*/
  return buffered_web_time_ranges_;
  // FIXME
}

double WebMediaPlayerGst::maxTimeSeekable() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // If we haven't even gotten to ReadyStateHaveMetadata yet then just
  // return 0 so that the seekable range is empty.
  if (ready_state_ < WebMediaPlayer::ReadyStateHaveMetadata)
    return 0.0;

  // We don't support seeking in streaming media.
  if (data_source_ && data_source_->IsStreaming())
    return 0.0;
  return duration();
}

bool WebMediaPlayerGst::didLoadingProgress() {
  DCHECK(main_loop_->BelongsToCurrentThread());
  bool pipeline_progress = true;  // FIXME
  bool data_progress = buffered_data_source_host_.DidLoadingProgress();
  return pipeline_progress || data_progress;
}

void WebMediaPlayerGst::paint(WebCanvas* canvas,
                              const WebRect& rect,
                              unsigned char alpha) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  TRACE_EVENT0("media", "WebMediaPlayerGst:paint");

  if (!accelerated_compositing_reported_) {
    accelerated_compositing_reported_ = true;
    // Normally paint() is only called in non-accelerated rendering, but there
    // are exceptions such as webgl where compositing is used in the WebView but
    // video frames are still rendered to a canvas.
    UMA_HISTOGRAM_BOOLEAN(
        "Media.AcceleratedCompositingActive",
        frame_->view()->isAcceleratedCompositingActive());
  }

  // TODO(scherkus): Clarify paint() API contract to better understand when and
  // why it's being called. For example, today paint() is called when:
  //   - We haven't reached HAVE_CURRENT_DATA and need to paint black
  //   - We're painting to a canvas
  // See http://crbug.com/341225 http://crbug.com/342621 for details.
  scoped_refptr<media::VideoFrame> video_frame =
      GetCurrentFrameFromCompositor();

  gfx::Rect gfx_rect(rect);
  skcanvas_video_renderer_.Paint(video_frame.get(), canvas, gfx_rect, alpha);
}

bool WebMediaPlayerGst::hasSingleSecurityOrigin() const {
  if (data_source_)
    return data_source_->HasSingleOrigin();
  return true;
}

bool WebMediaPlayerGst::didPassCORSAccessCheck() const {
  if (data_source_)
    return data_source_->DidPassCORSAccessCheck();
  return false;
}

double WebMediaPlayerGst::mediaTimeForTimeValue(double timeValue) const {
  return ConvertSecondsToTimestamp(timeValue).InSecondsF();
}

unsigned WebMediaPlayerGst::decodedFrameCount() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME
  return 0;
}

unsigned WebMediaPlayerGst::droppedFrameCount() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME
  return 0;
}

unsigned WebMediaPlayerGst::audioDecodedByteCount() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME
  return 0;
}

unsigned WebMediaPlayerGst::videoDecodedByteCount() const {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME
  return 0;
}

bool WebMediaPlayerGst::copyVideoTextureToPlatformTexture(
    blink::WebGraphicsContext3D* web_graphics_context,
    unsigned int texture,
    unsigned int level,
    unsigned int internal_format,
    unsigned int type,
    bool premultiply_alpha,
    bool flip_y) {
  TRACE_EVENT0("media", "WebMediaPlayerGst:copyVideoTextureToPlatformTexture");

  scoped_refptr<media::VideoFrame> video_frame =
      GetCurrentFrameFromCompositor();

  if (!video_frame)
    return false;
  if (video_frame->format() != media::VideoFrame::NATIVE_TEXTURE)
    return false;

  const gpu::MailboxHolder* mailbox_holder = video_frame->mailbox_holder();
  if (mailbox_holder->texture_target != GL_TEXTURE_2D)
    return false;

  // Since this method changes which texture is bound to the TEXTURE_2D target,
  // ideally it would restore the currently-bound texture before returning.
  // The cost of getIntegerv is sufficiently high, however, that we want to
  // avoid it in user builds. As a result assume (below) that |texture| is
  // bound when this method is called, and only verify this fact when
  // DCHECK_IS_ON.
#if DCHECK_IS_ON
  GLint bound_texture = 0;
  web_graphics_context->getIntegerv(GL_TEXTURE_BINDING_2D, &bound_texture);
  DCHECK_EQ(static_cast<GLuint>(bound_texture), texture);
#endif

  uint32 source_texture = web_graphics_context->createTexture();

  web_graphics_context->waitSyncPoint(mailbox_holder->sync_point);
  web_graphics_context->bindTexture(GL_TEXTURE_2D, source_texture);
  web_graphics_context->consumeTextureCHROMIUM(GL_TEXTURE_2D,
                                               mailbox_holder->mailbox.name);

  // The video is stored in a unmultiplied format, so premultiply
  // if necessary.
  web_graphics_context->pixelStorei(GL_UNPACK_PREMULTIPLY_ALPHA_CHROMIUM,
                                    premultiply_alpha);
  // Application itself needs to take care of setting the right flip_y
  // value down to get the expected result.
  // flip_y==true means to reverse the video orientation while
  // flip_y==false means to keep the intrinsic orientation.
  web_graphics_context->pixelStorei(GL_UNPACK_FLIP_Y_CHROMIUM, flip_y);
  web_graphics_context->copyTextureCHROMIUM(GL_TEXTURE_2D,
                                            source_texture,
                                            texture,
                                            level,
                                            internal_format,
                                            type);
  web_graphics_context->pixelStorei(GL_UNPACK_FLIP_Y_CHROMIUM, false);
  web_graphics_context->pixelStorei(GL_UNPACK_PREMULTIPLY_ALPHA_CHROMIUM,
                                    false);

  // Restore the state for TEXTURE_2D binding point as mentioned above.
  web_graphics_context->bindTexture(GL_TEXTURE_2D, texture);

  web_graphics_context->deleteTexture(source_texture);
  web_graphics_context->flush();
  video_frame->AppendReleaseSyncPoint(web_graphics_context->insertSyncPoint());
  return true;
}

// Helper enum for reporting generateKeyRequest/addKey histograms.
enum MediaKeyException {
  kUnknownResultId,
  kSuccess,
  kKeySystemNotSupported,
  kInvalidPlayerState,
  kMaxMediaKeyException
};

WebMediaPlayer::MediaKeyException
WebMediaPlayerGst::generateKeyRequest(const WebString& key_system,
                                      const unsigned char* init_data,
                                      unsigned init_data_length) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME: Add EME support
  return WebMediaPlayer::MediaKeyExceptionKeySystemNotSupported;
}

WebMediaPlayer::MediaKeyException WebMediaPlayerGst::addKey(
    const WebString& key_system,
    const unsigned char* key,
    unsigned key_length,
    const unsigned char* init_data,
    unsigned init_data_length,
    const WebString& session_id) {
  // FIXME: Support EME
  return WebMediaPlayer::MediaKeyExceptionKeySystemNotSupported;
}

WebMediaPlayer::MediaKeyException WebMediaPlayerGst::cancelKeyRequest(
    const WebString& key_system,
    const WebString& session_id) {

  // FIXME: Support EME
  return WebMediaPlayer::MediaKeyExceptionKeySystemNotSupported;
}

void WebMediaPlayerGst::setContentDecryptionModule(
    blink::WebContentDecryptionModule* cdm) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME: Support EME
  return;
}

void WebMediaPlayerGst::InvalidateOnMainThread() {
  DCHECK(main_loop_->BelongsToCurrentThread());
  TRACE_EVENT0("media", "WebMediaPlayerGst::InvalidateOnMainThread");

  client_->repaint();
}

#if 0
void WebMediaPlayerGst::OnPipelineSeek(PipelineStatus status) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  starting_ = false;
  seeking_ = false;
  if (pending_seek_) {
    pending_seek_ = false;
    seek(pending_seek_seconds_);
    return;
  }

  if (status != media::PIPELINE_OK) {
    OnPipelineError(status);
    return;
  }

  // Update our paused time.
  // FIXME: Get time from pipeline
  if (paused_)
    paused_time_ = media::kInfiniteDuration();

  client_->timeChanged();
}

void WebMediaPlayerGst::OnPipelineEnded() {
  DCHECK(main_loop_->BelongsToCurrentThread());
  client_->timeChanged();
}

void WebMediaPlayerGst::OnPipelineError(PipelineStatus error) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  DCHECK_NE(error, media::PIPELINE_OK);

  if (ready_state_ == WebMediaPlayer::ReadyStateHaveNothing) {
    // Any error that occurs before reaching ReadyStateHaveMetadata should
    // be considered a format error.
    SetNetworkState(WebMediaPlayer::NetworkStateFormatError);

    // TODO(scherkus): This should be handled by HTMLMediaElement and controls
    // should know when to invalidate themselves http://crbug.com/337015
    InvalidateOnMainThread();
    return;
  }

  SetNetworkState(PipelineErrorToNetworkState(error));

  if (error == media::PIPELINE_ERROR_DECRYPT)
    EmeUMAHistogramCounts(current_key_system_, "DecryptError", 1);

  // TODO(scherkus): This should be handled by HTMLMediaElement and controls
  // should know when to invalidate themselves http://crbug.com/337015
  InvalidateOnMainThread();
}

void WebMediaPlayerGst::OnPipelineMetadata(
    media::PipelineMetadata metadata) {
  DVLOG(1) << "OnPipelineMetadata";

  pipeline_metadata_ = metadata;

  SetReadyState(WebMediaPlayer::ReadyStateHaveMetadata);

  if (hasVideo()) {
    DCHECK(!video_weblayer_);
    video_weblayer_.reset(
        new webkit::WebLayerImpl(cc::VideoLayer::Create(compositor_)));
    video_weblayer_->setOpaque(opaque_);
    client_->setWebLayer(video_weblayer_.get());
  }

  // TODO(scherkus): This should be handled by HTMLMediaElement and controls
  // should know when to invalidate themselves http://crbug.com/337015
  InvalidateOnMainThread();
}

void WebMediaPlayerGst::OnPipelinePrerollCompleted() {
  DVLOG(1) << "OnPipelinePrerollCompleted";

  // Only transition to ReadyStateHaveEnoughData if we don't have
  // any pending seeks because the transition can cause Blink to
  // report that the most recent seek has completed.
  if (!pending_seek_) {
    SetReadyState(WebMediaPlayer::ReadyStateHaveEnoughData);

    // TODO(scherkus): This should be handled by HTMLMediaElement and controls
    // should know when to invalidate themselves http://crbug.com/337015
    InvalidateOnMainThread();
  }
}
#endif

void WebMediaPlayerGst::OnDemuxerOpened() {
  DCHECK(main_loop_->BelongsToCurrentThread());
  client_->mediaSourceOpened(new WebMediaSourceImpl(
      NULL, base::Bind(&LogMediaSourceError, media_log_)));
  // FIXME: Need to pass a non-NULL WebMediaSource implementation which supports
  // https://dvcs.w3.org/hg/html-media/raw-file/default/media-source/media-source.html#widl-MediaSource-addSourceBuffer-SourceBuffer-DOMString-type
}

void WebMediaPlayerGst::OnAddTextTrack(
    const media::TextTrackConfig& config,
    const media::AddTextTrackDoneCB& done_cb) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  const WebInbandTextTrackImpl::Kind web_kind =
      static_cast<WebInbandTextTrackImpl::Kind>(config.kind());
  const blink::WebString web_label =
      blink::WebString::fromUTF8(config.label());
  const blink::WebString web_language =
      blink::WebString::fromUTF8(config.language());
  const blink::WebString web_id =
      blink::WebString::fromUTF8(config.id());

  scoped_ptr<WebInbandTextTrackImpl> web_inband_text_track(
      new WebInbandTextTrackImpl(web_kind, web_label, web_language, web_id,
                                 text_track_index_++));

  scoped_ptr<media::TextTrack> text_track(
      new TextTrackImpl(main_loop_, client_, web_inband_text_track.Pass()));

  done_cb.Run(text_track.Pass());
}

void WebMediaPlayerGst::DataSourceInitialized(const GURL& gurl, bool success) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  if (!success) {
    SetNetworkState(WebMediaPlayer::NetworkStateFormatError);

    // TODO(scherkus): This should be handled by HTMLMediaElement and controls
    // should know when to invalidate themselves http://crbug.com/337015
    InvalidateOnMainThread();
    return;
  }

  StartPipeline();
}

void WebMediaPlayerGst::NotifyDownloading(bool is_downloading) {
  if (!is_downloading && network_state_ == WebMediaPlayer::NetworkStateLoading)
    SetNetworkState(WebMediaPlayer::NetworkStateIdle);
  else if (is_downloading && network_state_ == WebMediaPlayer::NetworkStateIdle)
    SetNetworkState(WebMediaPlayer::NetworkStateLoading);
  media_log_->AddEvent(
      media_log_->CreateBooleanEvent(
          media::MediaLogEvent::NETWORK_ACTIVITY_SET,
          "is_downloading_data", is_downloading));
}

void WebMediaPlayerGst::StartPipeline() {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // Keep track if this is a MSE or non-MSE playback.
  UMA_HISTOGRAM_BOOLEAN("Media.MSE.Playback",
                        (load_type_ == LoadTypeMediaSource));

  // FIXME: Implement me
}

void WebMediaPlayerGst::SetNetworkState(WebMediaPlayer::NetworkState state) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  DVLOG(1) << "SetNetworkState: " << state;
  network_state_ = state;
  // Always notify to ensure client has the latest value.
  client_->networkStateChanged();
}

void WebMediaPlayerGst::SetReadyState(WebMediaPlayer::ReadyState state) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  DVLOG(1) << "SetReadyState: " << state;

  if (state == WebMediaPlayer::ReadyStateHaveEnoughData &&
      is_local_source_ &&
      network_state_ == WebMediaPlayer::NetworkStateLoading)
    SetNetworkState(WebMediaPlayer::NetworkStateLoaded);

  ready_state_ = state;
  // Always notify to ensure client has the latest value.
  client_->readyStateChanged();
}

// TODO: remove?
blink::WebAudioSourceProvider* WebMediaPlayerGst::audioSourceProvider() {
  return NULL;
}

void WebMediaPlayerGst::IncrementExternallyAllocatedMemory() {
  DCHECK(main_loop_->BelongsToCurrentThread());
  incremented_externally_allocated_memory_ = true;
  v8::Isolate::GetCurrent()->AdjustAmountOfExternalAllocatedMemory(
      kPlayerExtraMemory);
}

void WebMediaPlayerGst::OnDurationChanged() {
  if (ready_state_ == WebMediaPlayer::ReadyStateHaveNothing)
    return;

  client_->durationChanged();
}

void WebMediaPlayerGst::OnNaturalSizeChanged(gfx::Size size) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  DCHECK_NE(ready_state_, WebMediaPlayer::ReadyStateHaveNothing);
  TRACE_EVENT0("media", "WebMediaPlayerGst::OnNaturalSizeChanged");

  media_log_->AddEvent(
      media_log_->CreateVideoSizeSetEvent(size.width(), size.height()));
  // FIXME: Set pipeline size

  client_->sizeChanged();
}

void WebMediaPlayerGst::OnOpacityChanged(bool opaque) {
  DCHECK(main_loop_->BelongsToCurrentThread());
  DCHECK_NE(ready_state_, WebMediaPlayer::ReadyStateHaveNothing);

  opaque_ = opaque;
  if (video_weblayer_)
    video_weblayer_->setOpaque(opaque_);
}

void WebMediaPlayerGst::FrameReady(
    const scoped_refptr<media::VideoFrame>& frame) {
  compositor_task_runner_->PostTask(
      FROM_HERE,
      base::Bind(&VideoFrameCompositor::UpdateCurrentFrame,
                 base::Unretained(compositor_),
                 frame));
}

void WebMediaPlayerGst::SetDecryptorReadyCB(
     const media::DecryptorReadyCB& decryptor_ready_cb) {
  DCHECK(main_loop_->BelongsToCurrentThread());

  // FIXME: Unsupported
  return;
}

static void GetCurrentFrameAndSignal(
    VideoFrameCompositor* compositor,
    scoped_refptr<media::VideoFrame>* video_frame_out,
    base::WaitableEvent* event) {
  TRACE_EVENT0("media", "GetCurrentFrameAndSignal");
  *video_frame_out = compositor->GetCurrentFrame();
  event->Signal();
}

scoped_refptr<media::VideoFrame>
WebMediaPlayerGst::GetCurrentFrameFromCompositor() {
  TRACE_EVENT0("media", "WebMediaPlayerGst::GetCurrentFrameFromCompositor");
  if (compositor_task_runner_->BelongsToCurrentThread())
    return compositor_->GetCurrentFrame();

  // Use a posted task and waitable event instead of a lock otherwise
  // WebGL/Canvas can see different content than what the compositor is seeing.
  scoped_refptr<media::VideoFrame> video_frame;
  base::WaitableEvent event(false, false);
  compositor_task_runner_->PostTask(FROM_HERE,
                                    base::Bind(&GetCurrentFrameAndSignal,
                                               base::Unretained(compositor_),
                                               &video_frame,
                                               &event));
  event.Wait();
  return video_frame;
}

}  // namespace content
