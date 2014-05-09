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

#include "formfieldrestrictedvalues.h"

#include <assert.h>
#include <QDebug>
#include <QMap>
#include <QWebElement>

namespace artemis
{

FormRestrictions FormFieldRestrictedValues::getRestrictions(QList<FormFieldDescriptorConstPtr> formFields, ArtemisWebPagePtr page)
{
    QSet<SelectRestriction> selects;
    QMap<QString, RadioRestriction > radioGroups;

    // Loop through form fields and add them to selects or radios (or ignore) as appropriate.
    foreach(FormFieldDescriptorConstPtr field, formFields) {
        if (field->getType() == FIXED_INPUT) {
            SelectRestriction result;
            result.variable = getVariableName(field);
            QWebElementCollection options = field->getDomElement()->getElement(page).findAll("option");
            foreach(QWebElement o, options) {
                result.values.append(o.attribute("value"));
            }
            selects.insert(result);

        } else if (field->getDomElement()->getElement(page).attribute("type") == "radio") {
            QString varName = getVariableName(field);
            QString groupName = field->getDomElement()->getName();

            // radioGroups[groupName] gives a default constructed RadioRestriction if groupName is not yet in the map.
            radioGroups[groupName].groupName = groupName;
            radioGroups[groupName].variables.insert(varName);
            radioGroups[groupName].alwaysSet = radioGroups[groupName].alwaysSet || field->getDomElement()->getElement(page).hasAttribute("checked");

        }
    }

    return FormRestrictions(selects, radioGroups.values().toSet());
}

bool FormFieldRestrictedValues::safeForIntegerCoercion(FormRestrictions restrictions, QString variable)
{
    QString name = variable;
    name.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    // A variable is only unsafe to coerce (according to the FormRestrictions) if it has a select restriction with a value which cannot be coerced to a valid integer.
    foreach(SelectRestriction sr, restrictions.first) {
        if(sr.variable == name) {
            foreach(QString value, sr.values) {
                // TODO: Would prefer to use a more general regex (e.g. allowing zero-padded values or leading/trailing
                // spaces) but these values cannot currently be injected back correctly (even though we could coerce
                // and solve them), so we are quite conservative for now.
                if(!value.contains(QRegExp("^(0|([1-9][0-9]*))$"))) {
                    return false;
                }
            }
        }
    }
    return true;
}




// Returns the variable name used for a given field (id or name).
QString FormFieldRestrictedValues::getVariableName(FormFieldDescriptorConstPtr field)
{
    if (!field->getDomElement()->getId().isEmpty()) {
        return field->getDomElement()->getId();
    }

    if (!field->getDomElement()->getName().isEmpty()) {
        return field->getDomElement()->getName();
    }

    // If there is no id and no name, this is an error. All form fields should have an auto-generated id at least by now.
    qDebug() << "Warning, form field with no corresponding variable name found.\n";
    return "NO-NAME";
}



} // namespace artemis
