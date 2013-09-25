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


#include "imageviewerdialog.h"


namespace artemis
{


// Add the ImageViewerWidget with this image and any buttons/controls we need.
ImageViewerDialog::ImageViewerDialog(QString filename, QWidget *parent)
    : QDialog(parent)
{
    QVBoxLayout* layout = new QVBoxLayout();
    mImageView = new ImageViewerWidget(filename);

    // Set up the zooming buttons
    QPushButton* zoomIn = new QPushButton("+");
    QPushButton* zoomOut = new QPushButton("-");
    QPushButton* zoomOrig = new QPushButton("1:1");
    QObject::connect(zoomIn, SIGNAL(released()), mImageView, SLOT(slZoomIn()));
    QObject::connect(zoomOut, SIGNAL(released()), mImageView, SLOT(slZoomOut()));
    QObject::connect(zoomOrig, SIGNAL(released()), mImageView, SLOT(slZoomOriginal()));
    zoomIn->setSizePolicy(QSizePolicy::Fixed, QSizePolicy::Fixed);
    zoomOut->setSizePolicy(QSizePolicy::Fixed, QSizePolicy::Fixed);
    zoomOrig->setSizePolicy(QSizePolicy::Fixed, QSizePolicy::Fixed);
    zoomIn->setMaximumWidth(28);
    zoomOut->setMaximumWidth(28);
    zoomOrig->setMaximumWidth(28);

    QHBoxLayout* zoomLayout = new QHBoxLayout();
    zoomLayout->addWidget(zoomIn);
    zoomLayout->addWidget(zoomOut);
    zoomLayout->addWidget(zoomOrig);
    zoomLayout->addStretch();
    layout->addLayout(zoomLayout);

    // The image widget itself.
    layout->addWidget(mImageView);

    // The Ok button.
    QDialogButtonBox* dialogButtons = new QDialogButtonBox(QDialogButtonBox::Ok, Qt::Horizontal, this);
    QObject::connect(dialogButtons, SIGNAL(accepted()), this, SLOT(accept()));
    layout->addWidget(dialogButtons);

    setLayout(layout);

    // Dialog properties.
    setWindowTitle(QString("Viewing %1").arg(filename));
    setSizeGripEnabled(true);
}


} // namespace artmeis

