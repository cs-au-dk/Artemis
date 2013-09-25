/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include "initialanalysiswidget.h"


namespace artemis
{


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


} //namespace artemis
