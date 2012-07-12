/*
 * Copyright (C) 2011 Apple Inc. All rights reserved.
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
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. AND ITS CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL APPLE INC. OR ITS CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "config.h"
#include "Download.h"

using namespace WebCore;

namespace WebKit {

void Download::platformDidFinish()
{
    ASSERT(!m_bundlePath.isEmpty());
    ASSERT(!m_destination.isEmpty());

    // Try to move the bundle to the final filename.
    DWORD flags = MOVEFILE_COPY_ALLOWED | (m_allowOverwrite ? MOVEFILE_REPLACE_EXISTING : 0);
    if (::MoveFileExW(m_bundlePath.charactersWithNullTermination(), m_destination.charactersWithNullTermination(), flags))
        return;

    // The move failed. Give the client one more chance to choose the final filename.
    m_destination = retrieveDestinationWithSuggestedFilename(m_destination, m_allowOverwrite);
    if (m_destination.isEmpty())
        return;

    // We either need to report our final filename as the bundle filename or the updated destination filename.
    flags = MOVEFILE_COPY_ALLOWED | (m_allowOverwrite ? MOVEFILE_REPLACE_EXISTING : 0);
    if (::MoveFileExW(m_bundlePath.charactersWithNullTermination(), m_destination.charactersWithNullTermination(), flags))
        didCreateDestination(m_destination);
    else
        didCreateDestination(m_bundlePath);
}

} // namespace WebKit
