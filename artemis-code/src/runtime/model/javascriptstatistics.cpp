
#include "statistics/statsstorage.h"

#include "javascriptstatistics.h"

namespace artemis {

JavascriptStatistics::JavascriptStatistics(QObject* parent) : QObject(parent)
{
}

void JavascriptStatistics::slJavascriptPropertyRead(QString propertyName)
{
    statistics()->accumulate("WebKit::readproperties", 1);
}

void JavascriptStatistics::slJavascriptPropertyWritten(QString propertyName)
{
    statistics()->accumulate("WebKit::writtenproperties", 1);
}

}
