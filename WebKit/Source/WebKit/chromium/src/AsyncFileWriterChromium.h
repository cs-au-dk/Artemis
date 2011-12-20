/*
 * Copyright (C) 2010 Google Inc. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following disclaimer
 * in the documentation and/or other materials provided with the
 * distribution.
 *     * Neither the name of Google Inc. nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef AsyncFileWriterChromium_h
#define AsyncFileWriterChromium_h

#if ENABLE(FILE_SYSTEM)

#include "AsyncFileWriter.h"
#include "WebFileError.h"
#include "WebFileWriterClient.h"
#include <wtf/PassOwnPtr.h>

namespace WebKit {
class WebFileWriter;
}

namespace WebCore {

class Blob;
class AsyncFileWriterClient;

class AsyncFileWriterChromium : public AsyncFileWriter, public WebKit::WebFileWriterClient {
public:
    AsyncFileWriterChromium(AsyncFileWriterClient* client);
    ~AsyncFileWriterChromium();
    
    void setWebFileWriter(PassOwnPtr<WebKit::WebFileWriter> writer);

    // FileWriter
    virtual void write(long long position, Blob* data);
    virtual void truncate(long long length);
    virtual void abort();

    // WebFileWriterClient
    virtual void didWrite(long long bytes, bool complete);
    virtual void didTruncate();
    virtual void didFail(WebKit::WebFileError);

private:
    OwnPtr<WebKit::WebFileWriter> m_writer;
    AsyncFileWriterClient* m_client;
};

} // namespace

#endif // ENABLE(FILE_SYSTEM)

#endif // AsyncFileWriterChromium_h
