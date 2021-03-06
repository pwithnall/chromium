// Copyright 2014 The Chromium Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#ifndef UI_GFX_OZONE_SURFACE_OZONE_H_
#define UI_GFX_OZONE_SURFACE_OZONE_H_

#include "base/basictypes.h"
#include "base/memory/scoped_ptr.h"
#include "skia/ext/refptr.h"
#include "ui/gfx/gfx_export.h"

class SkCanvas;

namespace gfx {

class Size;
class VSyncProvider;

// The platform-specific part of an EGL surface or software output.
//
// This class owns any bits that the ozone implementation needs freed when
// the software output or EGL surface is destroyed.
//
// If you want to paint on a window with ozone, you need to create a
// SurfaceOzone for that window.
//
// The platform can support software, EGL, or both for painting on the
// window. The initializer for unsupported modes should return false.
class GFX_EXPORT SurfaceOzone {
 public:
  virtual ~SurfaceOzone() {}

  // Initialize the surface for output using EGL/GLES2. Returns true if
  // initialization was successful.
  virtual bool InitializeEGL() = 0;

  // Returns the EGL native window for rendering onto this surface.
  // This can be used to to create a GLSurface.
  virtual intptr_t /* EGLNativeWindowType */ GetEGLNativeWindow() = 0;

  // Initialize canvas for software output. Returns true if initialization
  // was successful.
  virtual bool InitializeCanvas() = 0;

  // Returns an SkCanvas for drawing on the window. The canvas is intended
  // for use when no EGL/GLES2 acceleration is possible.
  virtual skia::RefPtr<SkCanvas> GetCanvas() = 0;

  // Attempts to resize the canvas to match the viewport size. Returns true if
  // resizing was successful, otherwise false (platforms may require a fixed
  // size canvas). After resizing, the compositor must call GetCanvas() to get
  // the next canvas.
  virtual bool ResizeCanvas(const gfx::Size& viewport_size) = 0;

  // Present the current canvas. After presenting, the compositor must call
  // GetCanvas() to get the next canvas.
  virtual bool PresentCanvas() = 0;

  // Returns a gfx::VsyncProvider for this surface. Note that this may be
  // called after we have entered the sandbox so if there are operations (e.g.
  // opening a file descriptor providing vsync events) that must be done
  // outside of the sandbox, they must have been completed in
  // InitializeHardware. Returns an empty scoped_ptr on error.
  virtual scoped_ptr<gfx::VSyncProvider> CreateVSyncProvider() = 0;
};

}  // namespace gfx

#endif  // UI_GFX_OZONE_SURFACE_OZONE_H_
