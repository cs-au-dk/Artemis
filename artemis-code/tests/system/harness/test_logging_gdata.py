
# TODO: This logger can no longer work.
# It uses the GData v2 API, which is no longer available.
# https://developers.google.com/sheets/api/v3/
# https://github.com/google/gdata-python-client/blob/master/src/gdata/client.py#L23

import subprocess
import re
import getpass
import sys

try
    import gdata.spreadsheet.service
except ImportError:
    print "The 'gdata' module is required to save the results."
    print "See http://code.google.com/p/gdata-python-client/ for downloads."
    sys.exit()


# Google Spreadsheets Logging
class GDataLogger():
    """
    Allows logging to a google spreadsheet.
    New data is simply appended to the table as a new row.
    New columns are added as required.
    """
    
    def __init__(self, spreadsheet_key, worksheet_id):
        # If no worksheet_id is given, the GData API uses the default worksheet in the given spreadsheet instead.
        # However, this does not seem to be working, so we require it for now.
        # Also it is assumed we have one when we update the worksheet size. We could add 'od6' as the default.
        self._spreadsheet_key = spreadsheet_key
        self._worksheet_id = worksheet_id
        self._isopen = False
        self.blank_row = True # Insert a blank row before any logging is done, to visually separate tests.
    
    # TODO: This is a hack. We should use some of the proper authentication APIs instead.
    def open_spreadsheet(self, email=None, password=None):
        """Ask the user for their Google accopunt and password and open the spreadsheet."""
        
        self._sheet = gdata.spreadsheet.service.SpreadsheetsService()
        if email:
            self._sheet.email = email
        else:
            self._sheet.email = raw_input("Please enter your google account (email): ")
        if password:
            self._sheet.password = password
        else:
            self._sheet.password = getpass.getpass("Please enter your password: ")
        self._sheet.source = "ArtForm Test Logger"
        try:
            self._sheet.ProgrammaticLogin()
        except gdata.service.BadAuthentication as e:
            print "Failed to log in:", e.message
            sys.exit()
        
        print "Login successful."
        self._isopen = True
        
        if self.blank_row:
            self.log_data({'Testing Run':' '}) # Completely blank rows are not allowed to be written

    def log_data(self, data):
        """Takes a dictionary mapping column names to values and appends it to the spreadsheet."""
        assert(self._isopen)
        
        # Make sure the columns exist
        self._ensure_columns_exist(data.keys())
        
        # Fix the column names
        data = self._prepare_new_row(data)

        # Add the row to the spreadsheet
        entry = self._sheet.InsertRow(data, self._spreadsheet_key, self._worksheet_id)
        assert(isinstance(entry, gdata.spreadsheet.SpreadsheetsList)) # Whether or not we successfully added the row.

    @staticmethod
    def _prepare_new_row(data):
        """
        Take a dict of the column headers and values to be inserted and makes the dictionary keys suitable for passing
        to the GData API.
        """
        # Column names must exist and they are given lower-case and must be converted to valid XML element names.
        # Colons are used for namespacing so they are also not allowed in the column name part.
        # If column names have duplicate encodings they will be numbered, which is hard to handle here.
        # So I am assuming all column names will be unique, even after this transformation.
        # This includes column names which are already in the spreadsheet but which are not in this data set.
        invalid_chars = "!\"#$%&'()*+,/;<=>?@[\]^`{|}~"
        invalid_start_chars = "-.0123456789"
        disallowed_by_google_api = ":"
        
        strip_expression = re.compile(r"\s+|[" + re.escape(invalid_chars + disallowed_by_google_api) + r"]+|^[" + re.escape(invalid_start_chars) + "]+")
        
        processed_data = {}
        for column, value in data.iteritems():
            column_api_name = re.sub(strip_expression, '', column.lower())
            processed_data[column_api_name] = value
        
        return processed_data

    def _ensure_columns_exist(self, desired_columns):
        """
        If the given columns are not present in the spreadsheet, we add them. Input is a dict mapping column names in the
        API format to the literal values.
        """
        assert(self._isopen)
        
        # Get the existing columns
        query = gdata.spreadsheet.service.CellQuery()
        query.max_row = '1'
        query.min_row = '1'
        header_cells = self._sheet.GetCellsFeed(self._spreadsheet_key, self._worksheet_id, query=query)
        columns = [cell.content.text for cell in header_cells.entry]
        last_col_no = max([int(cell.cell.col) for cell in header_cells.entry])
        
        # Work out which we need to add
        new_columns = set(desired_columns) - set(columns)
        
        # Resize the worksheet if necessary
        # Because we use the list feed to add rows, we only need to worry about the width here.
        work_sheet = self._sheet.GetWorksheetsFeed(self._spreadsheet_key, self._worksheet_id)
        if(last_col_no + len(new_columns) > int(work_sheet.col_count.text)):
            work_sheet.col_count.text = str(last_col_no + len(new_columns))
            try:
                self._sheet.UpdateWorksheet(work_sheet)
            except gdata.service.RequestError:
                print "Error resizing worksheet."
                assert(false) # Fail this test.
        
        # Add them
        try:
            for new_col in new_columns:
                last_col_no += 1
                self._sheet.UpdateCell(1, last_col_no, new_col, self._spreadsheet_key, self._worksheet_id)
        except gdata.service.RequestError:
            print "Error adding a new column header. (maybe there is not enough space on the worksheet?)"
            assert(false) # Fail the current test
    
    def process_header(self, string):
        return string.replace("::", "::\n")
    


# Checking the currently checked out git commit.

def current_git_commit():
    """Fetches the current Git commit sha, or None if it is not available."""
    try:
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"]).strip()
    except CalledProcessError:
        commit = None
    return commit

def current_git_commit_hyperlink():
    """Fetches the current Git commit and returns a link in the Google Docs format to that commit."""
    commit = current_git_commit()
    if commit:
        link = "https://github.com/cs-au-dk/Artemis/commit/%s" % commit
        return "=hyperlink(\"%s\", \"%s\")" % (link, commit[:8])
    else:
        return ""
