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



#include "imageviewerwidget.h"

namespace artemis
{



ImageViewerWidget::ImageViewerWidget(QString filename, QWidget* parent)
    : QScrollArea(parent),
      mPixmap(filename)
{
    mImage = new QLabel;
    mImage->setPixmap(mPixmap);

    setWidget(mImage);

    mImage->setScaledContents(true);
    mOriginalSize = mImage->size();
}


// The zoom factor.
qreal ImageViewerWidget::mZoomAmount = 1.5;

// Scales the image up by mZoomAmount
void ImageViewerWidget::slZoomIn()
{
    mImage->resize(mImage->size() * mZoomAmount);
}

// Scales the image down by mZoomAmount
void ImageViewerWidget::slZoomOut()
{
    mImage->resize(mImage->size() / mZoomAmount);
}

// Reset the scale to 100%
void ImageViewerWidget::slZoomOriginal()
{
    mImage->resize(mOriginalSize);
}


} //namespace artemis
