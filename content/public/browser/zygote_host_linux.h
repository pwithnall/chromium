// Copyright (c) 2012 The Chromium Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#ifndef CONTENT_PUBLIC_BROWSER_ZYGOTE_HOST_LINUX_H_
#define CONTENT_PUBLIC_BROWSER_ZYGOTE_HOST_LINUX_H_
#pragma once

#include <unistd.h>

#include "base/process.h"
#include "content/common/content_export.h"

namespace content {

// http://code.google.com/p/chromium/wiki/LinuxZygote

// The zygote host is the interface, in the browser process, to the zygote
// process.
class ZygoteHost {
 public:
  // Returns the singleton instance.
  CONTENT_EXPORT static ZygoteHost* GetInstance();

  // These form a bitmask which describes the conditions of the sandbox that
  // the zygote finds itself in.
  enum {
    kSandboxSUID = 1 << 0,     // SUID sandbox active
    kSandboxPIDNS = 1 << 1,    // SUID sandbox is using the PID namespace
    kSandboxNetNS = 1 << 2,    // SUID sandbox is using the network namespace
    kSandboxSeccomp = 1 << 3,  // seccomp sandbox active.
  };

  virtual pid_t GetPid() const = 0;

  // Returns an int which is a bitmask of kSandbox* values. Only valid after
  // the first render has been forked.
  virtual int GetSandboxStatus() const = 0;

  // Adjust the OOM score of the given renderer's PID.  The allowed
  // range for the score is [0, 1000], where higher values are more
  // likely to be killed by the OOM killer.
  virtual void AdjustRendererOOMScore(base::ProcessHandle process_handle,
                                      int score) = 0;
};

}  // namespace content

#endif  // CONTENT_PUBLIC_BROWSER_ZYGOTE_HOST_LINUX_H_
