// Copyright 2013 The Chromium Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "media/cdm/ppapi/cdm_adapter.h"

#include <cstring>
#include <string>
#include <vector>

#include "base/basictypes.h"
#include "base/compiler_specific.h"
#include "media/cdm/ppapi/api/content_decryption_module.h"
#include "media/cdm/ppapi/cdm_helpers.h"
#include "ppapi/c/pp_errors.h"
#include "ppapi/c/pp_stdint.h"
#include "ppapi/c/private/pp_content_decryptor.h"
#include "ppapi/cpp/completion_callback.h"
#include "ppapi/cpp/core.h"
#include "ppapi/cpp/instance.h"
#include "ppapi/cpp/logging.h"
#include "ppapi/cpp/module.h"
#include "ppapi/cpp/pass_ref.h"
#include "ppapi/cpp/resource.h"
#include "ppapi/cpp/var.h"
#include "ppapi/cpp/var_array_buffer.h"
#include "ppapi/utility/completion_callback_factory.h"

#if defined(CHECK_DOCUMENT_URL)
#include "ppapi/cpp/dev/url_util_dev.h"
#include "ppapi/cpp/instance_handle.h"
#endif  // defined(CHECK_DOCUMENT_URL)

namespace {

bool IsMainThread() {
  return pp::Module::Get()->core()->IsMainThread();
}

// Posts a task to run |cb| on the main thread. The task is posted even if the
// current thread is the main thread.
void PostOnMain(pp::CompletionCallback cb) {
  pp::Module::Get()->core()->CallOnMainThread(0, cb, PP_OK);
}

// Ensures |cb| is called on the main thread, either because the current thread
// is the main thread or by posting it to the main thread.
void CallOnMain(pp::CompletionCallback cb) {
  // TODO(tomfinegan): This is only necessary because PPAPI doesn't allow calls
  // off the main thread yet. Remove this once the change lands.
  if (IsMainThread())
    cb.Run(PP_OK);
  else
    PostOnMain(cb);
}

// Configures a cdm::InputBuffer. |subsamples| must exist as long as
// |input_buffer| is in use.
void ConfigureInputBuffer(
    const pp::Buffer_Dev& encrypted_buffer,
    const PP_EncryptedBlockInfo& encrypted_block_info,
    std::vector<cdm::SubsampleEntry>* subsamples,
    cdm::InputBuffer* input_buffer) {
  PP_DCHECK(subsamples);
  PP_DCHECK(!encrypted_buffer.is_null());

  input_buffer->data = static_cast<uint8_t*>(encrypted_buffer.data());
  input_buffer->data_size = encrypted_block_info.data_size;
  PP_DCHECK(encrypted_buffer.size() >=
            static_cast<uint32_t>(input_buffer->data_size));
  input_buffer->data_offset = encrypted_block_info.data_offset;

  PP_DCHECK(encrypted_block_info.key_id_size <=
            arraysize(encrypted_block_info.key_id));
  input_buffer->key_id_size = encrypted_block_info.key_id_size;
  input_buffer->key_id = input_buffer->key_id_size > 0 ?
      encrypted_block_info.key_id : NULL;

  PP_DCHECK(encrypted_block_info.iv_size <= arraysize(encrypted_block_info.iv));
  input_buffer->iv_size = encrypted_block_info.iv_size;
  input_buffer->iv = encrypted_block_info.iv_size > 0 ?
      encrypted_block_info.iv : NULL;

  input_buffer->num_subsamples = encrypted_block_info.num_subsamples;
  if (encrypted_block_info.num_subsamples > 0) {
    subsamples->reserve(encrypted_block_info.num_subsamples);

    for (uint32_t i = 0; i < encrypted_block_info.num_subsamples; ++i) {
      subsamples->push_back(cdm::SubsampleEntry(
          encrypted_block_info.subsamples[i].clear_bytes,
          encrypted_block_info.subsamples[i].cipher_bytes));
    }

    input_buffer->subsamples = &(*subsamples)[0];
  }

  input_buffer->timestamp = encrypted_block_info.tracking_info.timestamp;
}

PP_DecryptResult CdmStatusToPpDecryptResult(cdm::Status status) {
  switch (status) {
    case cdm::kSuccess:
      return PP_DECRYPTRESULT_SUCCESS;
    case cdm::kNoKey:
      return PP_DECRYPTRESULT_DECRYPT_NOKEY;
    case cdm::kNeedMoreData:
      return PP_DECRYPTRESULT_NEEDMOREDATA;
    case cdm::kDecryptError:
      return PP_DECRYPTRESULT_DECRYPT_ERROR;
    case cdm::kDecodeError:
      return PP_DECRYPTRESULT_DECODE_ERROR;
    default:
      PP_NOTREACHED();
      return PP_DECRYPTRESULT_DECODE_ERROR;
  }
}

PP_DecryptedFrameFormat CdmVideoFormatToPpDecryptedFrameFormat(
    cdm::VideoFormat format) {
  switch (format) {
    case cdm::kYv12:
      return PP_DECRYPTEDFRAMEFORMAT_YV12;
    case cdm::kI420:
      return PP_DECRYPTEDFRAMEFORMAT_I420;
    default:
      return PP_DECRYPTEDFRAMEFORMAT_UNKNOWN;
  }
}

cdm::AudioDecoderConfig::AudioCodec PpAudioCodecToCdmAudioCodec(
    PP_AudioCodec codec) {
  switch (codec) {
    case PP_AUDIOCODEC_VORBIS:
      return cdm::AudioDecoderConfig::kCodecVorbis;
    case PP_AUDIOCODEC_AAC:
      return cdm::AudioDecoderConfig::kCodecAac;
    default:
      return cdm::AudioDecoderConfig::kUnknownAudioCodec;
  }
}

cdm::VideoDecoderConfig::VideoCodec PpVideoCodecToCdmVideoCodec(
    PP_VideoCodec codec) {
  switch (codec) {
    case PP_VIDEOCODEC_VP8:
      return cdm::VideoDecoderConfig::kCodecVp8;
    case PP_VIDEOCODEC_H264:
      return cdm::VideoDecoderConfig::kCodecH264;
    default:
      return cdm::VideoDecoderConfig::kUnknownVideoCodec;
  }
}

cdm::VideoDecoderConfig::VideoCodecProfile PpVCProfileToCdmVCProfile(
    PP_VideoCodecProfile profile) {
  switch (profile) {
    case PP_VIDEOCODECPROFILE_VP8_MAIN:
      return cdm::VideoDecoderConfig::kVp8ProfileMain;
    case PP_VIDEOCODECPROFILE_H264_BASELINE:
      return cdm::VideoDecoderConfig::kH264ProfileBaseline;
    case PP_VIDEOCODECPROFILE_H264_MAIN:
      return cdm::VideoDecoderConfig::kH264ProfileMain;
    case PP_VIDEOCODECPROFILE_H264_EXTENDED:
      return cdm::VideoDecoderConfig::kH264ProfileExtended;
    case PP_VIDEOCODECPROFILE_H264_HIGH:
      return cdm::VideoDecoderConfig::kH264ProfileHigh;
    case PP_VIDEOCODECPROFILE_H264_HIGH_10:
      return cdm::VideoDecoderConfig::kH264ProfileHigh10;
    case PP_VIDEOCODECPROFILE_H264_HIGH_422:
      return cdm::VideoDecoderConfig::kH264ProfileHigh422;
    case PP_VIDEOCODECPROFILE_H264_HIGH_444_PREDICTIVE:
      return cdm::VideoDecoderConfig::kH264ProfileHigh444Predictive;
    default:
      return cdm::VideoDecoderConfig::kUnknownVideoCodecProfile;
  }
}

cdm::VideoFormat PpDecryptedFrameFormatToCdmVideoFormat(
    PP_DecryptedFrameFormat format) {
  switch (format) {
    case PP_DECRYPTEDFRAMEFORMAT_YV12:
      return cdm::kYv12;
    case PP_DECRYPTEDFRAMEFORMAT_I420:
      return cdm::kI420;
    default:
      return cdm::kUnknownVideoFormat;
  }
}

cdm::StreamType PpDecryptorStreamTypeToCdmStreamType(
    PP_DecryptorStreamType stream_type) {
  switch (stream_type) {
    case PP_DECRYPTORSTREAMTYPE_AUDIO:
      return cdm::kStreamTypeAudio;
    case PP_DECRYPTORSTREAMTYPE_VIDEO:
      return cdm::kStreamTypeVideo;
  }

  PP_NOTREACHED();
  return cdm::kStreamTypeVideo;
}

}  // namespace

namespace media {

CdmAdapter::CdmAdapter(PP_Instance instance, pp::Module* module)
    : pp::Instance(instance),
      pp::ContentDecryptor_Private(this),
      allocator_(this),
      cdm_(NULL) {
  callback_factory_.Initialize(this);
}

CdmAdapter::~CdmAdapter() {}

bool CdmAdapter::CreateCdmInstance(const std::string& key_system) {
  PP_DCHECK(!cdm_);
  cdm_ = make_linked_ptr(CdmWrapper::Create(
      key_system.data(), key_system.size(), GetCdmHost, this));
  return (cdm_ != NULL);
}

// No KeyErrors should be reported in this function because they cannot be
// bubbled up in the WD EME API. Those errors will be reported during session
// creation (aka GenerateKeyRequest).
void CdmAdapter::Initialize(const std::string& key_system,
                            bool can_challenge_platform) {
  PP_DCHECK(!key_system.empty());
  PP_DCHECK(key_system_.empty() || (key_system_ == key_system && cdm_));

  if (!cdm_ && !CreateCdmInstance(key_system))
    return;

  PP_DCHECK(cdm_);
  key_system_ = key_system;
}

void CdmAdapter::GenerateKeyRequest(const std::string& type,
                                    pp::VarArrayBuffer init_data) {
  // Initialize() doesn't report an error, so GenerateKeyRequest() can be called
  // even if Initialize() failed.
  if (!cdm_) {
    SendUnknownKeyError(key_system_, std::string());
    return;
  }

#if defined(CHECK_DOCUMENT_URL)
  PP_URLComponents_Dev url_components = {};
  pp::Var href = pp::URLUtil_Dev::Get()->GetDocumentURL(
      pp::InstanceHandle(pp_instance()), &url_components);
  PP_DCHECK(href.is_string());
  PP_DCHECK(!href.AsString().empty());
  PP_DCHECK(url_components.host.begin);
  PP_DCHECK(0 < url_components.host.len);
#endif  // defined(CHECK_DOCUMENT_URL)

  cdm::Status status = cdm_->GenerateKeyRequest(
      type.data(), type.size(),
      static_cast<const uint8_t*>(init_data.Map()),
      init_data.ByteLength());
  PP_DCHECK(status == cdm::kSuccess || status == cdm::kSessionError);
  if (status != cdm::kSuccess)
    SendUnknownKeyError(key_system_, std::string());
}

void CdmAdapter::AddKey(const std::string& session_id,
                        pp::VarArrayBuffer key,
                        pp::VarArrayBuffer init_data) {
  // TODO(jrummell): In EME WD, AddKey() can only be called on valid sessions.
  // We should be able to DCHECK(cdm_) when addressing http://crbug.com/249976.
  if (!cdm_) {
    SendUnknownKeyError(key_system_, session_id);
    return;
  }

  const uint8_t* key_ptr = static_cast<const uint8_t*>(key.Map());
  int key_size = key.ByteLength();
  const uint8_t* init_data_ptr = static_cast<const uint8_t*>(init_data.Map());
  int init_data_size = init_data.ByteLength();
  PP_DCHECK(!init_data_ptr == !init_data_size);

  if (!key_ptr || key_size <= 0) {
    SendUnknownKeyError(key_system_, session_id);
    return;
  }

  cdm::Status status = cdm_->AddKey(session_id.data(), session_id.size(),
                                    key_ptr, key_size,
                                    init_data_ptr, init_data_size);
  PP_DCHECK(status == cdm::kSuccess || status == cdm::kSessionError);
  if (status != cdm::kSuccess) {
    SendUnknownKeyError(key_system_, session_id);
    return;
  }

  SendKeyAdded(key_system_, session_id);
}

void CdmAdapter::CancelKeyRequest(const std::string& session_id) {
  // TODO(jrummell): In EME WD, AddKey() can only be called on valid sessions.
  // We should be able to DCHECK(cdm_) when addressing http://crbug.com/249976.
  if (!cdm_) {
    SendUnknownKeyError(key_system_, session_id);
    return;
  }

  cdm::Status status = cdm_->CancelKeyRequest(session_id.data(),
                                              session_id.size());
  PP_DCHECK(status == cdm::kSuccess || status == cdm::kSessionError);
  if (status != cdm::kSuccess)
    SendUnknownKeyError(key_system_, session_id);
}

// Note: In the following decryption/decoding related functions, errors are NOT
// reported via KeyError, but are reported via corresponding PPB calls.

void CdmAdapter::Decrypt(pp::Buffer_Dev encrypted_buffer,
                         const PP_EncryptedBlockInfo& encrypted_block_info) {
  PP_DCHECK(!encrypted_buffer.is_null());

  // Release a buffer that the caller indicated it is finished with.
  allocator_.Release(encrypted_block_info.tracking_info.buffer_id);

  cdm::Status status = cdm::kDecryptError;
  LinkedDecryptedBlock decrypted_block(new DecryptedBlockImpl());

  if (cdm_) {
    cdm::InputBuffer input_buffer;
    std::vector<cdm::SubsampleEntry> subsamples;
    ConfigureInputBuffer(encrypted_buffer, encrypted_block_info, &subsamples,
                         &input_buffer);
    status = cdm_->Decrypt(input_buffer, decrypted_block.get());
    PP_DCHECK(status != cdm::kSuccess ||
              (decrypted_block->DecryptedBuffer() &&
               decrypted_block->DecryptedBuffer()->Size()));
  }

  CallOnMain(callback_factory_.NewCallback(
      &CdmAdapter::DeliverBlock,
      status,
      decrypted_block,
      encrypted_block_info.tracking_info));
}

void CdmAdapter::InitializeAudioDecoder(
    const PP_AudioDecoderConfig& decoder_config,
    pp::Buffer_Dev extra_data_buffer) {
  cdm::Status status = cdm::kSessionError;
  if (cdm_) {
    cdm::AudioDecoderConfig cdm_decoder_config;
    cdm_decoder_config.codec =
        PpAudioCodecToCdmAudioCodec(decoder_config.codec);
    cdm_decoder_config.channel_count = decoder_config.channel_count;
    cdm_decoder_config.bits_per_channel = decoder_config.bits_per_channel;
    cdm_decoder_config.samples_per_second = decoder_config.samples_per_second;
    cdm_decoder_config.extra_data =
        static_cast<uint8_t*>(extra_data_buffer.data());
    cdm_decoder_config.extra_data_size =
        static_cast<int32_t>(extra_data_buffer.size());
    status = cdm_->InitializeAudioDecoder(cdm_decoder_config);
  }

  CallOnMain(callback_factory_.NewCallback(
      &CdmAdapter::DecoderInitializeDone,
      PP_DECRYPTORSTREAMTYPE_AUDIO,
      decoder_config.request_id,
      status == cdm::kSuccess));
}

void CdmAdapter::InitializeVideoDecoder(
    const PP_VideoDecoderConfig& decoder_config,
    pp::Buffer_Dev extra_data_buffer) {
  cdm::Status status = cdm::kSessionError;
  if (cdm_) {
    cdm::VideoDecoderConfig cdm_decoder_config;
    cdm_decoder_config.codec =
        PpVideoCodecToCdmVideoCodec(decoder_config.codec);
    cdm_decoder_config.profile =
        PpVCProfileToCdmVCProfile(decoder_config.profile);
    cdm_decoder_config.format =
        PpDecryptedFrameFormatToCdmVideoFormat(decoder_config.format);
    cdm_decoder_config.coded_size.width = decoder_config.width;
    cdm_decoder_config.coded_size.height = decoder_config.height;
    cdm_decoder_config.extra_data =
        static_cast<uint8_t*>(extra_data_buffer.data());
    cdm_decoder_config.extra_data_size =
        static_cast<int32_t>(extra_data_buffer.size());
    status = cdm_->InitializeVideoDecoder(cdm_decoder_config);
  }

  CallOnMain(callback_factory_.NewCallback(
      &CdmAdapter::DecoderInitializeDone,
      PP_DECRYPTORSTREAMTYPE_VIDEO,
      decoder_config.request_id,
      status == cdm::kSuccess));
}

void CdmAdapter::DeinitializeDecoder(PP_DecryptorStreamType decoder_type,
                                     uint32_t request_id) {
  PP_DCHECK(cdm_);  // InitializeXxxxxDecoder should have succeeded.
  if (cdm_) {
    cdm_->DeinitializeDecoder(
        PpDecryptorStreamTypeToCdmStreamType(decoder_type));
  }

  CallOnMain(callback_factory_.NewCallback(
      &CdmAdapter::DecoderDeinitializeDone,
      decoder_type,
      request_id));
}

void CdmAdapter::ResetDecoder(PP_DecryptorStreamType decoder_type,
                              uint32_t request_id) {
  PP_DCHECK(cdm_);  // InitializeXxxxxDecoder should have succeeded.
  if (cdm_)
    cdm_->ResetDecoder(PpDecryptorStreamTypeToCdmStreamType(decoder_type));

  CallOnMain(callback_factory_.NewCallback(&CdmAdapter::DecoderResetDone,
                                           decoder_type,
                                           request_id));
}

void CdmAdapter::DecryptAndDecode(
    PP_DecryptorStreamType decoder_type,
    pp::Buffer_Dev encrypted_buffer,
    const PP_EncryptedBlockInfo& encrypted_block_info) {
  PP_DCHECK(cdm_);  // InitializeXxxxxDecoder should have succeeded.
  // Release a buffer that the caller indicated it is finished with.
  allocator_.Release(encrypted_block_info.tracking_info.buffer_id);

  cdm::InputBuffer input_buffer;
  std::vector<cdm::SubsampleEntry> subsamples;
  if (cdm_ && !encrypted_buffer.is_null()) {
    ConfigureInputBuffer(encrypted_buffer,
                         encrypted_block_info,
                         &subsamples,
                         &input_buffer);
  }

  cdm::Status status = cdm::kDecodeError;

  switch (decoder_type) {
    case PP_DECRYPTORSTREAMTYPE_VIDEO: {
      LinkedVideoFrame video_frame(new VideoFrameImpl());
      if (cdm_)
        status = cdm_->DecryptAndDecodeFrame(input_buffer, video_frame.get());
      CallOnMain(callback_factory_.NewCallback(
          &CdmAdapter::DeliverFrame,
          status,
          video_frame,
          encrypted_block_info.tracking_info));
      return;
    }

    case PP_DECRYPTORSTREAMTYPE_AUDIO: {
      LinkedAudioFrames audio_frames(new AudioFramesImpl());
      if (cdm_) {
        status = cdm_->DecryptAndDecodeSamples(input_buffer,
                                               audio_frames.get());
      }
      CallOnMain(callback_factory_.NewCallback(
          &CdmAdapter::DeliverSamples,
          status,
          audio_frames,
          encrypted_block_info.tracking_info));
      return;
    }

    default:
      PP_NOTREACHED();
      return;
  }
}

cdm::Buffer* CdmAdapter::Allocate(int32_t capacity) {
  return allocator_.Allocate(capacity);
}

void CdmAdapter::SetTimer(int64_t delay_ms, void* context) {
  // NOTE: doesn't really need to run on the main thread; could just as well run
  // on a helper thread if |cdm_| were thread-friendly and care was taken.  We
  // only use CallOnMainThread() here to get delayed-execution behavior.
  pp::Module::Get()->core()->CallOnMainThread(
      delay_ms,
      callback_factory_.NewCallback(&CdmAdapter::TimerExpired, context),
      PP_OK);
}

void CdmAdapter::TimerExpired(int32_t result, void* context) {
  PP_DCHECK(result == PP_OK);
  cdm_->TimerExpired(context);
}

double CdmAdapter::GetCurrentWallTimeInSeconds() {
  return pp::Module::Get()->core()->GetTime();
}

void CdmAdapter::SendKeyMessage(
    const char* session_id, int32_t session_id_length,
    const char* message, int32_t message_length,
    const char* default_url, int32_t default_url_length) {
  PP_DCHECK(!key_system_.empty());
  PostOnMain(callback_factory_.NewCallback(
      &CdmAdapter::KeyMessage,
      SessionInfo(key_system_,
                  std::string(session_id, session_id_length)),
      std::vector<uint8>(message, message + message_length),
      std::string(default_url, default_url_length)));
}

void CdmAdapter::SendKeyError(const char* session_id,
                              int32_t session_id_length,
                              cdm::MediaKeyError error_code,
                              uint32_t system_code) {
  SendKeyErrorInternal(key_system_,
                       std::string(session_id, session_id_length),
                       error_code,
                       system_code);
}

void CdmAdapter::GetPrivateData(int32_t* instance,
                                cdm::Host::GetPrivateInterface* get_interface) {
  *instance = pp_instance();
  *get_interface = pp::Module::Get()->get_browser_interface();
}

void CdmAdapter::SendUnknownKeyError(const std::string& key_system,
                                     const std::string& session_id) {
  SendKeyErrorInternal(key_system, session_id, cdm::kUnknownError, 0);
}

void CdmAdapter::SendKeyAdded(const std::string& key_system,
                              const std::string& session_id) {
  PostOnMain(callback_factory_.NewCallback(
      &CdmAdapter::KeyAdded,
      SessionInfo(key_system_, session_id)));
}

void CdmAdapter::SendKeyErrorInternal(const std::string& key_system,
                                      const std::string& session_id,
                                      cdm::MediaKeyError error_code,
                                      uint32_t system_code) {
  PostOnMain(callback_factory_.NewCallback(&CdmAdapter::KeyError,
                                           SessionInfo(key_system_, session_id),
                                           error_code,
                                           system_code));
}

void CdmAdapter::KeyAdded(int32_t result, const SessionInfo& session_info) {
  PP_DCHECK(result == PP_OK);
  PP_DCHECK(!session_info.key_system.empty());
  pp::ContentDecryptor_Private::KeyAdded(session_info.key_system,
                                         session_info.session_id);
}

void CdmAdapter::KeyMessage(int32_t result,
                            const SessionInfo& session_info,
                            const std::vector<uint8>& message,
                            const std::string& default_url) {
  PP_DCHECK(result == PP_OK);
  PP_DCHECK(!session_info.key_system.empty());

  pp::VarArrayBuffer message_array_buffer(message.size());
  if (message.size() > 0) {
    memcpy(message_array_buffer.Map(), message.data(), message.size());
  }

  pp::ContentDecryptor_Private::KeyMessage(
      session_info.key_system, session_info.session_id,
      message_array_buffer, default_url);
}

void CdmAdapter::KeyError(int32_t result,
                          const SessionInfo& session_info,
                          cdm::MediaKeyError error_code,
                          uint32_t system_code) {
  PP_DCHECK(result == PP_OK);
  pp::ContentDecryptor_Private::KeyError(
      session_info.key_system, session_info.session_id,
      error_code, system_code);
}

void CdmAdapter::DeliverBlock(int32_t result,
                              const cdm::Status& status,
                              const LinkedDecryptedBlock& decrypted_block,
                              const PP_DecryptTrackingInfo& tracking_info) {
  PP_DCHECK(result == PP_OK);
  PP_DecryptedBlockInfo decrypted_block_info;
  decrypted_block_info.tracking_info = tracking_info;
  decrypted_block_info.tracking_info.timestamp = decrypted_block->Timestamp();
  decrypted_block_info.tracking_info.buffer_id = 0;
  decrypted_block_info.data_size = 0;
  decrypted_block_info.result = CdmStatusToPpDecryptResult(status);

  pp::Buffer_Dev buffer;

  if (decrypted_block_info.result == PP_DECRYPTRESULT_SUCCESS) {
    PP_DCHECK(decrypted_block.get() && decrypted_block->DecryptedBuffer());
    if (!decrypted_block.get() || !decrypted_block->DecryptedBuffer()) {
      PP_NOTREACHED();
      decrypted_block_info.result = PP_DECRYPTRESULT_DECRYPT_ERROR;
    } else {
      PpbBuffer* ppb_buffer =
          static_cast<PpbBuffer*>(decrypted_block->DecryptedBuffer());
      buffer = ppb_buffer->buffer_dev();
      decrypted_block_info.tracking_info.buffer_id = ppb_buffer->buffer_id();
      decrypted_block_info.data_size = ppb_buffer->Size();
    }
  }

  pp::ContentDecryptor_Private::DeliverBlock(buffer, decrypted_block_info);
}

void CdmAdapter::DecoderInitializeDone(int32_t result,
                                       PP_DecryptorStreamType decoder_type,
                                       uint32_t request_id,
                                       bool success) {
  PP_DCHECK(result == PP_OK);
  pp::ContentDecryptor_Private::DecoderInitializeDone(decoder_type,
                                                      request_id,
                                                      success);
}

void CdmAdapter::DecoderDeinitializeDone(int32_t result,
                                         PP_DecryptorStreamType decoder_type,
                                         uint32_t request_id) {
  pp::ContentDecryptor_Private::DecoderDeinitializeDone(decoder_type,
                                                        request_id);
}

void CdmAdapter::DecoderResetDone(int32_t result,
                                  PP_DecryptorStreamType decoder_type,
                                  uint32_t request_id) {
  pp::ContentDecryptor_Private::DecoderResetDone(decoder_type, request_id);
}

void CdmAdapter::DeliverFrame(
    int32_t result,
    const cdm::Status& status,
    const LinkedVideoFrame& video_frame,
    const PP_DecryptTrackingInfo& tracking_info) {
  PP_DCHECK(result == PP_OK);
  PP_DecryptedFrameInfo decrypted_frame_info;
  decrypted_frame_info.tracking_info.request_id = tracking_info.request_id;
  decrypted_frame_info.tracking_info.buffer_id = 0;
  decrypted_frame_info.result = CdmStatusToPpDecryptResult(status);

  pp::Buffer_Dev buffer;

  if (decrypted_frame_info.result == PP_DECRYPTRESULT_SUCCESS) {
    if (!IsValidVideoFrame(video_frame)) {
      PP_NOTREACHED();
      decrypted_frame_info.result = PP_DECRYPTRESULT_DECODE_ERROR;
    } else {
      PpbBuffer* ppb_buffer =
          static_cast<PpbBuffer*>(video_frame->FrameBuffer());

      buffer = ppb_buffer->buffer_dev();

      decrypted_frame_info.tracking_info.timestamp = video_frame->Timestamp();
      decrypted_frame_info.tracking_info.buffer_id = ppb_buffer->buffer_id();
      decrypted_frame_info.format =
          CdmVideoFormatToPpDecryptedFrameFormat(video_frame->Format());
      decrypted_frame_info.width = video_frame->Size().width;
      decrypted_frame_info.height = video_frame->Size().height;
      decrypted_frame_info.plane_offsets[PP_DECRYPTEDFRAMEPLANES_Y] =
          video_frame->PlaneOffset(cdm::VideoFrame::kYPlane);
      decrypted_frame_info.plane_offsets[PP_DECRYPTEDFRAMEPLANES_U] =
          video_frame->PlaneOffset(cdm::VideoFrame::kUPlane);
      decrypted_frame_info.plane_offsets[PP_DECRYPTEDFRAMEPLANES_V] =
          video_frame->PlaneOffset(cdm::VideoFrame::kVPlane);
      decrypted_frame_info.strides[PP_DECRYPTEDFRAMEPLANES_Y] =
          video_frame->Stride(cdm::VideoFrame::kYPlane);
      decrypted_frame_info.strides[PP_DECRYPTEDFRAMEPLANES_U] =
          video_frame->Stride(cdm::VideoFrame::kUPlane);
      decrypted_frame_info.strides[PP_DECRYPTEDFRAMEPLANES_V] =
          video_frame->Stride(cdm::VideoFrame::kVPlane);
    }
  }
  pp::ContentDecryptor_Private::DeliverFrame(buffer, decrypted_frame_info);
}

void CdmAdapter::DeliverSamples(int32_t result,
                                const cdm::Status& status,
                                const LinkedAudioFrames& audio_frames,
                                const PP_DecryptTrackingInfo& tracking_info) {
  PP_DCHECK(result == PP_OK);

  PP_DecryptedBlockInfo decrypted_block_info;
  decrypted_block_info.tracking_info = tracking_info;
  decrypted_block_info.tracking_info.timestamp = 0;
  decrypted_block_info.tracking_info.buffer_id = 0;
  decrypted_block_info.data_size = 0;
  decrypted_block_info.result = CdmStatusToPpDecryptResult(status);

  pp::Buffer_Dev buffer;

  if (decrypted_block_info.result == PP_DECRYPTRESULT_SUCCESS) {
    PP_DCHECK(audio_frames.get() && audio_frames->FrameBuffer());
    if (!audio_frames.get() || !audio_frames->FrameBuffer()) {
      PP_NOTREACHED();
      decrypted_block_info.result = PP_DECRYPTRESULT_DECRYPT_ERROR;
    } else {
      PpbBuffer* ppb_buffer =
          static_cast<PpbBuffer*>(audio_frames->FrameBuffer());
      buffer = ppb_buffer->buffer_dev();
      decrypted_block_info.tracking_info.buffer_id = ppb_buffer->buffer_id();
      decrypted_block_info.data_size = ppb_buffer->Size();
    }
  }

  pp::ContentDecryptor_Private::DeliverSamples(buffer, decrypted_block_info);
}

bool CdmAdapter::IsValidVideoFrame(const LinkedVideoFrame& video_frame) {
  if (!video_frame.get() ||
      !video_frame->FrameBuffer() ||
      (video_frame->Format() != cdm::kI420 &&
       video_frame->Format() != cdm::kYv12)) {
    return false;
  }

  PpbBuffer* ppb_buffer = static_cast<PpbBuffer*>(video_frame->FrameBuffer());

  for (int i = 0; i < cdm::VideoFrame::kMaxPlanes; ++i) {
    int plane_height = (i == cdm::VideoFrame::kYPlane) ?
        video_frame->Size().height : (video_frame->Size().height + 1) / 2;
    cdm::VideoFrame::VideoPlane plane =
        static_cast<cdm::VideoFrame::VideoPlane>(i);
    if (ppb_buffer->Size() < video_frame->PlaneOffset(plane) +
                             plane_height * video_frame->Stride(plane)) {
      return false;
    }
  }

  return true;
}

void* GetCdmHost(int host_interface_version, void* user_data) {
  if (!host_interface_version || !user_data)
    return NULL;

  if (host_interface_version != cdm::kHostInterfaceVersion)
    return NULL;

  CdmAdapter* cdm_adapter = static_cast<CdmAdapter*>(user_data);
  return static_cast<cdm::Host*>(cdm_adapter);
}

// This object is the global object representing this plugin library as long
// as it is loaded.
class CdmAdapterModule : public pp::Module {
 public:
  CdmAdapterModule() : pp::Module() {
    // This function blocks the renderer thread (PluginInstance::Initialize()).
    // Move this call to other places if this may be a concern in the future.
    INITIALIZE_CDM_MODULE();
  }
  virtual ~CdmAdapterModule() {
    DeinitializeCdmModule();
  }

  virtual pp::Instance* CreateInstance(PP_Instance instance) {
    return new CdmAdapter(instance, this);
  }
};

}  // namespace media

namespace pp {

// Factory function for your specialization of the Module object.
Module* CreateModule() {
  return new media::CdmAdapterModule();
}

}  // namespace pp
