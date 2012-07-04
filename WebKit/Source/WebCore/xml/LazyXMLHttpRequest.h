#ifndef LazyXMLHttpRequest_h
#define LazyXMLHttpRequest_h

#include "ResourceRequest.h"
#include "ThreadableLoader.h"

namespace WebCore {

class ScriptExecutionContext;
class ThreadableLoaderClient;

#ifdef ARTEMIS

class LazyXMLHttpRequest {

public:
	LazyXMLHttpRequest(ScriptExecutionContext*, const ResourceRequest&, ThreadableLoaderClient*, ThreadableLoaderOptions&);
	void fire();

private:
	ScriptExecutionContext* m_context;
	ThreadableLoaderClient* m_loader;
	ResourceRequest m_request;
	ThreadableLoaderOptions m_options;

};

#endif

} // namespace WebCore

#endif // LazyXMLHttpRequest_h
