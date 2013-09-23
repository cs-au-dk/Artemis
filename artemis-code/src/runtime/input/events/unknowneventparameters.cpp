#include "unknowneventparameters.h"

namespace artemis{


UnknownEventParameters::UnknownEventParameters() : EventParameters()
{
}

QString UnknownEventParameters::getJsString() const {
    return QString("");
}

EventType UnknownEventParameters::getType() const{
    return UNKNOWN_EVENT;
}

}
