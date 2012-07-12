/*
 * Copyright (C) 2007 Apple Inc.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE COMPUTER, INC. ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL APPLE COMPUTER, INC. OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
 * OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
 */

#ifndef WebURLAuthenticationChallengeSender_h
#define WebURLAuthenticationChallengeSender_h

#include "WebKit.h"

#include <wtf/Forward.h>
#include <wtf/RefPtr.h>

namespace WebCore {
    class AuthenticationClient;
}

class DECLSPEC_UUID("5CACD637-F82F-491F-947A-5DCA38AA0FEA") WebURLAuthenticationChallengeSender
    : public IWebURLAuthenticationChallengeSender
{
public:
    static WebURLAuthenticationChallengeSender* createInstance(PassRefPtr<WebCore::AuthenticationClient>);
private:
    WebURLAuthenticationChallengeSender(PassRefPtr<WebCore::AuthenticationClient>);
    ~WebURLAuthenticationChallengeSender();
public:
    // IUnknown
    virtual HRESULT STDMETHODCALLTYPE QueryInterface(REFIID riid, void** ppvObject);
    virtual ULONG STDMETHODCALLTYPE AddRef(void);
    virtual ULONG STDMETHODCALLTYPE Release(void);

    // IWebURLAuthenticationChallengeSender
    virtual HRESULT STDMETHODCALLTYPE cancelAuthenticationChallenge(
        /* [in] */ IWebURLAuthenticationChallenge* challenge);

    virtual HRESULT STDMETHODCALLTYPE continueWithoutCredentialForAuthenticationChallenge(
        /* [in] */ IWebURLAuthenticationChallenge* challenge);

    virtual HRESULT STDMETHODCALLTYPE useCredential(
        /* [in] */ IWebURLCredential* credential, 
        /* [in] */ IWebURLAuthenticationChallenge* challenge);

    WebCore::AuthenticationClient* authenticationClient() const;

private:
    ULONG m_refCount;

    RefPtr<WebCore::AuthenticationClient> m_client;
};

#endif
