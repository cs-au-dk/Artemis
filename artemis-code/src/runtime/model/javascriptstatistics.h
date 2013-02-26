#ifndef JAVASCRIPTSTATISTICS_H
#define JAVASCRIPTSTATISTICS_H

#include <QObject>

namespace artemis {

class JavascriptStatistics : public QObject
{

    Q_OBJECT

public:
    JavascriptStatistics(QObject* parent);

public slots:
    void slJavascriptPropertyRead(QString propertyName);
    void slJavascriptPropertyWritten(QString propertyName);

};

}

#endif // JAVASCRIPTSTATISTICS_H
