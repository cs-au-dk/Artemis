/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
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



ImageViewerDialog::ImageViewerDialog(QString filename, QWidget *parent)
    : QDialog(parent)
{
    // Add the ImageViewerWidget with this image and any buttons/controls we need.
    mImageView = new ImageViewerWidget(filename);
    QVBoxLayout* layout = new QVBoxLayout();
    layout->addWidget(mImageView);

    QDialogButtonBox* buttons = new QDialogButtonBox(QDialogButtonBox::Ok, Qt::Horizontal, this);
    QObject::connect(buttons, SIGNAL(accepted()), this, SLOT(accept()));
    layout->addWidget(buttons);

    setLayout(layout);

    setWindowTitle(QString("Viewing %1").arg(filename));
}


} // namespace artmeis

