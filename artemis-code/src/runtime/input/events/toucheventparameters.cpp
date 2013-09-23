#include "toucheventparameters.h"
namespace artemis{


TouchEventParameters::TouchEventParameters() : EventParameters()
{
}

QString TouchEventParameters::getJsString() const {
    return QString("");
}

EventType TouchEventParameters::getType() const{
    return TOUCH_EVENT;
}

}
