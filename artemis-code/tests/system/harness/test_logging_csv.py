"""
A CSV data logger constructed to roughly mirror the API from GDataLogger in test_logging_gdata.py.
"""

import csv
import subprocess


class CsvLogger:
    def __init__(self):
        self._rows = []
    
    def log_data(self, data):
        self._rows.append(data)
    
    def process_header(self, string):
        return string.replace("\n", "")
    
    def save(self, file_name):
        initial_columns = ["Testing Run", "Artemis Version", "Site", "Extra Args", "URL", "Analysis", "DIADEM Time", "Entry Point", "Running Time", "Exit Code", "Iterations"]
        statistics_columns = set()
        for row in self._rows:
            statistics_columns.update(row.keys())
        statistics_columns.difference_update(initial_columns)
        all_columns = initial_columns + sorted(statistics_columns)
        
        with open(file_name, 'w') as f:
            writer = csv.DictWriter(f, fieldnames=all_columns, restval="")
            writer.writeheader()
            
            for row in self._rows:
                writer.writerow(row)
        




# Checking the currently checked out git commit.
# TODO: This doesn't really belong in this file...

def current_git_commit():
    """Fetches the current Git commit sha, or None if it is not available."""
    try:
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"]).strip()
    except CalledProcessError:
        commit = None
    return commit

def current_git_commit_hyperlink():
    """Fetches the current Git commit and returns a link to that commit."""
    # TODO: For CSV output, we just return the shortened SHA string.
    commit = current_git_commit()
    if commit:
        commit[:8]
    else:
        return ""



def demo():
    pass

if __name__ == "__main__":
    demo()
