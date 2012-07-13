#include "qjquerylistener.h"

using namespace std;

QJQueryListener::QJQueryListener(QObject * parent) :
	QObject(parent) {}


/*
std::string functionName = std::string(frame.calculatedFunctionName().ascii().data());
    JSC::CallFrame * cframe = frame.callFrame();

    emit functionCalled(cframe, functionName);

    */

