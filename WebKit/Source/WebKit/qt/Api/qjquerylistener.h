#ifndef QJQUERYLISTENER_H
#define QJQUERYLISTENER_H

class QWEBKIT_EXPORT QJQueryListener : public QObject
{
	Q_OBJECT

public:
	explicit QJQueryListener(QObject *parent = 0);

signals:
	void eventAdded(QWebElement element, QString event, QString selectors);
	void eventRemoved(QWebElement element, QString event);
};

#endif