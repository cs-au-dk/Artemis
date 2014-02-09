#include "seleniumeventexecutionstatistics.h"

#include <QDebug>

namespace artemis{

    void SeleniumEventExecutionStatistics::registerEventDescription(EventHandlerDescriptorConstPtr desc){
        qDebug() << "SELENIUM: Event description registered.";
        mRegisteredHandlers.append(desc);
    }

    void SeleniumEventExecutionStatistics::beginNewIteration(){
        qDebug() << "SELENIUM: Begin new selenium iteration.";
        mRegisteredHandlers.clear();
    }

    QString SeleniumEventExecutionStatistics::generateOutput(){
        qDebug() << "SELENIUM: Generating selenium output.";
        foreach(EventHandlerDescriptorConstPtr desc, mRegisteredHandlers){

        }

        return QString();
    }
}
