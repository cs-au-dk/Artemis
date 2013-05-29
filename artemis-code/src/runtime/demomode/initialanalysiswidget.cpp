#include "initialanalysiswidget.h"

InitialAnalysisWidget::InitialAnalysisWidget(QWidget *parent) :
    QGroupBox(parent)
{
    setTitle("Initial Analysis");

    // TODO: temp dummy implementation id a list of buttons!

    QVBoxLayout *layout = new QVBoxLayout;

    QPushButton* b1 = new QPushButton("Button 1");
    layout->addWidget(b1);
    QPushButton* b2 = new QPushButton("Button 2");
    layout->addWidget(b2);
    QPushButton* b3 = new QPushButton("Button 3");
    layout->addWidget(b3);

    this->setLayout(layout);
}
