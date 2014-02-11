#include "seleniumeventexecutionstatistics.h"

#include <QDebug>

namespace artemis{

    SeleniumEventExecutionStatistics::SeleniumEventExecutionStatistics(const QUrl& url){
        mUrl = url;
        qDebug() << "SELENIUM: initializing stats with url: " <<  url;
    }

    void SeleniumEventExecutionStatistics::registerEventDescription(EventHandlerDescriptorConstPtr desc){
        qDebug() << "SELENIUM: Event description registered at: " << desc->xPathToElement();
        mCurrentRegisteredHandlers->append(desc);
    }

    void SeleniumEventExecutionStatistics::beginNewIteration(){
        qDebug() << "SELENIUM: Begin new selenium iteration.";
        if(mCurrentRegisteredHandlers != NULL){
            mRegisteredHandlers.append(*mCurrentRegisteredHandlers);
        }
        mCurrentRegisteredHandlers = new QList<EventHandlerDescriptorPtr>();
    }

    void SeleniumEventExecutionStatistics::generateOutput(){
        qDebug() << "SELENIUM: Generating selenium output.";
        QList<SeleniumTableRow> rows;

        rows.append(SeleniumTableRow("open", mUrl.toString()));

        foreach(EventHandlerDescriptorConstPtr desc, mRegisteredHandlers.last()){
            rows.append(SeleniumTableRow(desc->getName(), desc->xPathToElement()));
        }

    }


}
