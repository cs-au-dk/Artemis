#include "toucheventparameters.h"
namespace artemis{


TouchEventParameters::TouchEventParameters() : EventParameters(NULL)
{
}

QString TouchEventParameters::jsString() const {
    return QString("");
}

EventType TouchEventParameters::type() const{
    return TOUCH_EVENT;
}

}
