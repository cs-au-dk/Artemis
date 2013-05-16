#include "unknowneventparameters.h"

namespace artemis{


UnknownEventParameters::UnknownEventParameters() : EventParameters(NULL)
{
}

QString UnknownEventParameters::jsString() const {
    return QString("");
}

EventType UnknownEventParameters::type() const{
    return UNKNOWN_EVENT;
}

}
