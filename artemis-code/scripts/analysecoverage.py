#!/usr/bin/env python

"""
Script summarizing code-coverage from Artemis stdout
"""

import sys
import re
import pprint

COVERAGE_START = re.compile(r'Coverage for source located at URL: (.*)  line')
COVERED_LINE = re.compile(r'>>>')
COVERAGE_STOP = re.compile(r'==== Source code loaded ====')

COMMENT_MATCH = re.compile(r'^//.*')
COMMENT_MATCH2 = re.compile(r'^/\*.*\*/')
FUNCTION_DECL = re.compile(r'^function .*')
SCOPE_END = re.compile(r'^}[)]*;?$')

def _coverage_parser(lines, result):
	line = lines.pop(0)
	match = COVERAGE_START.search(line)

	if match == None:
		print line
		raise Exception("Expected file coverage statement")

	file_id = match.group(1)

	result[file_id] = {'total_lines' : 0,
					   'lines_covered': 0}

	def _line_parser(lines, result):
		line = lines.pop(0).strip()
		
		if line.strip() != '' and \
		   COMMENT_MATCH.match(line) is None and \
		   COMMENT_MATCH2.match(line) is None and \
		   FUNCTION_DECL.match(line) is None and \
		   SCOPE_END.match(line) is None:
			# ignore blank lines
			# ignore // comments
			# ignore /* */ comments
			# ignore function declerations (not assignments of lambda functions)
			# ignore }, }; });, })); ect.

			# should be ignored but are not
			  # multiline comments
			  # multiline object assignments

			result[file_id]['total_lines'] += 1

			if COVERED_LINE.search(line) is not None:
				result[file_id]['lines_covered'] += 1

		elif COVERED_LINE.search(line) is not None:
			# ERROR, we ignored a line which was covered
			raise Exception('Covered line (%s) ignored' % line)

		if COVERAGE_START.search(lines[0]) is not None:
			# lookahead, are we about to start on a new file?
			return _coverage_parser

		if COVERAGE_STOP.search(lines[0]) is not None:
			# lookahead, is this the last line of coverage data?
			return None

		return _line_parser

	return _line_parser

def _outer_parser(lines, result):
	try:
		line = lines.pop(0)
	except IndexError:
		return None

	if 'Adding AJAX request:' in line:
		result['ajax_callbacks'] = result.get('ajax_callbacks', 0) + 1

	if '=== Coverage information for execution ===' in line:
		return _coverage_parser

	return _outer_parser

def parse(lines):
	result = {}
	_parser = _outer_parser
	
	while _parser is not None:
		_parser = _parser(lines, result)

	return result

if __name__ == '__main__':
	if len(sys.argv) < 2:
		print 'usage: %s <artemis output file>' % sys.argv[0]
		sys.exit(1)

	if len(sys.argv) == 3:
		offset = int(sys.argv[2])
	else:
		offset = 0

	output_file = open(sys.argv[1], 'r')

	result = parse(output_file.readlines()[offset:])

	output_file.close()

	pprint.pprint(result)