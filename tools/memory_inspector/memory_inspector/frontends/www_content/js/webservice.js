// Copyright 2014 The Chromium Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

webservice = new (function() {

this.AJAX_BASE_URL_ = '/ajax';

this.ajaxRequest = function(path, responseCallback, errorCallback, postArgs) {
  var reqType = postArgs ? 'POST' : 'GET';
  var reqData = postArgs ? JSON.stringify(postArgs) : '';

  $.ajax({
    url: this.AJAX_BASE_URL_ + path,
    type: reqType,
    data: reqData,
    success: responseCallback,
    dataType: 'json',
    error: function (xhr, ajaxOptions, thrownError) {
      console.log('------------------------');
      console.log('AJAX error (req: ' + path + ').');
      console.log('HTTP response: ' + xhr.status + ' ' + thrownError);
      console.log(xhr.responseText);
      if (errorCallback)
        errorCallback(xhr.status, xhr.responseText);
    }
  });
};

})();