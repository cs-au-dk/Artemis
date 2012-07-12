/*
 Copyright 2011 Simon Holm Jensen. All rights reserved.

 Redistribution and use in source and binary forms, with or without modification, are
 permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this list of
 conditions and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice, this list
 of conditions and the following disclaimer in the documentation and/or other materials
 provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
 WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
 CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 The views and conclusions contained in the software and documentation are those of the
 authors and should not be interpreted as representing official policies, either expressed
 or implied, of Simon Holm Jensen
 */

#include <QNetworkProxy>

#include "statistics/statsstorage.h"
#include "runtime/runtime.h"
#include "runtime/ajax/ajaxrequestlistener.h"
#include "runtime/browser/cookies/immutablecookiejar.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "strategies/inputgenerator/targets/targetgenerator.h"
#include "strategies/inputgenerator/randominputgenerator.h"
#include "strategies/termination/numberofiterationstermination.h"
#include "strategies/termination/terminationstrategy.h"
#include "strategies/prioritizer/constantprioritizer.h"

#include "options.h"
#include "builder.h"

namespace artemis {

Runtime* Builder::build(const Options& options, QUrl url) {

	if (!options.useProxy.isNull()) {
		QStringList parts = options.useProxy.split(QString(":"));

		QNetworkProxy proxy(QNetworkProxy::HttpProxy, parts.at(0),
				parts.at(1).toShort());
		QNetworkProxy::setApplicationProxy(proxy);
	}

	MultiplexListener* listener = new MultiplexListener(0);

	AjaxRequestListener* ajaxRequestListner = new AjaxRequestListener(NULL);

	ImmutableCookieJar *immutable_cookie_jar = new ImmutableCookieJar(
			options.presetCookies, url.host());
	ajaxRequestListner->setCookieJar(immutable_cookie_jar);

	JQueryListener* jqueryListener = new JQueryListener(NULL);

    QString appName;
    if(options.appName.isNull()){
        appName = "";
    } else {
        appName = options.appName;
    }

	WebKitExecutor* webkitExecutor = new WebKitExecutor(NULL,
			options.presetFormfields, listener, jqueryListener,
            ajaxRequestListner, appName);

	TargetGenerator* targetGenerator = new TargetGenerator(NULL,
			jqueryListener);

	InputGeneratorStrategy* generator = new RandomInputGenerator(NULL,
			targetGenerator, options.numberSameLength);

	PrioritizerStrategy* prioritizer = new ConstantPrioritizer(NULL);

	TerminationStrategy* termination = new NumberOfIterationsTermination(0,
			options.iterationLimit);

	return new Runtime(NULL, webkitExecutor, generator, prioritizer,
			termination, listener, options.dumpUrls);

}

} // END NAMESPACE
