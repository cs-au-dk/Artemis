#include "seleniumeventexecutionstatistics.h"

#include <QDebug>

namespace artemis{

    void SeleniumEventExecutionStatistics::registerEventDescription(EventHandlerDescriptorConstPtr desc){
        qDebug() << "Event description registered.";
        mRegisteredHandlers.append(desc);
    }

    void SeleniumEventExecutionStatistics::beginNewIteration(){
        qDebug() << "Begin new selenium iteration.";
        mRegisteredHandlers.clear();
    }

    QString SeleniumEventExecutionStatistics::generateOutput(){
        qDebug() << "Generating selenium output.";
        foreach(EventHandlerDescriptorConstPtr desc, mRegisteredHandlers){

        }

        return QString();
    }
}
