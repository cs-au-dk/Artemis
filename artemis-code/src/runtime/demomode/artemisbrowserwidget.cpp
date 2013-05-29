#include "artemisbrowserwidget.h"

ArtemisBrowserWidget::ArtemisBrowserWidget(QWidget* parent) :
    QGroupBox(parent)
{
    setTitle("Artemis Browser");

    // TODO: temp dummy implementation id a list of buttons!

    QVBoxLayout *layout = new QVBoxLayout;

    QPushButton* b1 = new QPushButton("Button 1");
    layout->addWidget(b1);
    QPushButton* b2 = new QPushButton("Button 2");
    layout->addWidget(b2);

    this->setLayout(layout);

}
