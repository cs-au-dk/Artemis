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
            // A small JS injection to make sure the value property is correctly set on all option elements.
            field->getDomElement()->getElement(page).evaluateJavaScript("for(i=0; i<this.length; i++){ this.options[i].value = this.options[i].value; }"); // Surprisingly not necessarily a no-op.
            // Read back the values.
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
                // TODO: Would prefer to use a more general regex (e.g. allowing leading/trailing spaces)
                // but these values cannot currently be injected back correctly (even though we could coerce
                // and solve them), so we are quite conservative for now.
                if(!value.contains(QRegExp("^([0-9]*)$"))) {
                    return false;
                }
            }
        }
    }
    return true;
}

bool FormFieldRestrictedValues::symbolReferencesSelect(FormRestrictions restrictions, QString identifier) {

    QString name = identifier;
    name.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    foreach (SelectRestriction sr, restrictions.first) {
        if (sr.variable == name) {
            return true;
        }
    }

    return false;
}


bool FormFieldRestrictedValues::isValidSelectValue(FormRestrictions restrictions, QString identifier, QString symbolvalue) {

    QString name = identifier;
    name.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    foreach (SelectRestriction sr, restrictions.first) {
        if (sr.variable == name && sr.values.contains(symbolvalue)) {
            return true;
        }
    }
    return false;

}

bool FormFieldRestrictedValues::fuzzyMatchSelectValue(FormRestrictions restrictions, QString identifier, std::string* symbolvalue) {

    QString name = identifier;
    name.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    QString value = QString::fromStdString(*symbolvalue);

    foreach (SelectRestriction sr, restrictions.first) {
        if (sr.variable == name) {

            if (sr.values.contains(value)) {
                return true;
            }

            // find the first match were the value matches the suffix of the valid values
            foreach (QString v, sr.values) {
                if (v.endsWith(value)) {
                    *symbolvalue = v.toStdString();
                    return true;
                }
            }

            return false;
        }
    }
    return false;

}


QPair<bool, SelectRestriction> FormFieldRestrictedValues::getRelevantSelectRestriction(FormRestrictions restrictions, QString identifier)
{
    QString name = identifier;
    name.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    foreach (SelectRestriction sr, restrictions.first) {
        if (sr.variable == name) {
            return QPair<bool, SelectRestriction>(true, sr);
        }
    }

    return QPair<bool, SelectRestriction>(false, SelectRestriction());
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



QDebug operator<<(QDebug dbg, const SelectRestriction& sr) {
    dbg.nospace() << "Select " << sr.variable << " from [" << sr.values.join(",") << "].";
    return dbg.space();
}

QDebug operator<<(QDebug dbg, const RadioRestriction& rr) {
    dbg.nospace() << "Radio " << rr.groupName << " options [" << QStringList(rr.variables.toList()).join(",") << "]" << (rr.alwaysSet ? "" : " NOT") << " always set.";
    return dbg.space();
}


} // namespace artemis
