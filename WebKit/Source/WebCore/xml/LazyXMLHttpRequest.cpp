
#include "config.h"
#include "XMLHttpRequest.h"
#include "LazyXMLHttpRequest.h"

#include "Blob.h"
#include "ContentSecurityPolicy.h"
#include "CrossOriginAccessControl.h"
#include "DOMFormData.h"
#include "DOMImplementation.h"
#include "Event.h"
#include "EventException.h"
#include "EventListener.h"
#include "EventNames.h"
#include "ExceptionCode.h"
#include "File.h"
#include "HTMLDocument.h"
#include "HTTPParsers.h"
#include "HTTPValidation.h"
#include "InspectorInstrumentation.h"
#include "MemoryCache.h"
#include "ResourceError.h"
#include "ResourceRequest.h"
#include "ScriptCallStack.h"
#include "ScriptProfile.h"
#include "SecurityOrigin.h"
#include "Settings.h"
#include "SharedBuffer.h"
#include "TextResourceDecoder.h"
#include "ThreadableLoader.h"
#include "XMLHttpRequestException.h"
#include "XMLHttpRequestProgressEvent.h"
#include "XMLHttpRequestUpload.h"
#include "LazyXMLHttpRequest.h"
#include "markup.h"
#include <wtf/ArrayBuffer.h>
#include <wtf/RefCountedLeakCounter.h>
#include <wtf/StdLibExtras.h>
#include <wtf/UnusedParam.h>
#include <wtf/text/CString.h>

namespace WebCore {

#ifdef ARTEMIS
LazyXMLHttpRequest::LazyXMLHttpRequest(ScriptExecutionContext* context,
		const ResourceRequest& request,
		ThreadableLoaderClient* loader,
		ThreadableLoaderOptions& options) {

	m_context = context;
	m_loader = loader;
	m_request = request;
	m_options = options;

}

void LazyXMLHttpRequest::fire() {
	ThreadableLoader::loadResourceSynchronously(m_context, m_request, *m_loader, m_options);
}

#endif

} // namespace WebCore
