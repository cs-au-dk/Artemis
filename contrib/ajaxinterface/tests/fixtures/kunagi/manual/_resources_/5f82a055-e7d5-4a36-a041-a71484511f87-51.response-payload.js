var WikiParser = Editor.Parser = (function() {

	var run = 0;

	function log(message) {
		//if (console && run <= 2)
		//	console.log(message);
	}

	var tokenizeWiki = (function() {

		function next(source) {
			if (source.endOfLine())
				throw "end-of-line";
			var ch = source.next();
			// log("consumed: '" + ch + "'");
			return ch;
		}

		function reset(source) {
			var s = source.get();
			// log("reset: " + s);
			source.push(s);
		}

		function header(depth) {
			var endmarker = ' ';
			for (i = 0; i < depth; i++) {
				endmarker += '=';
			}
			return function(source, setState) {
				// log("header(" + source.peek() + ")")
				for (i = 0; i < depth; i++) {
					next(source);
				}
				next(source);
				// log("header-1(" + source.peek() + ")")
				var marker = '';
				while (!source.endOfLine()) {
					var ch = next(source);
					if (ch == ' ') {
						marker = ' ';
						continue;
					}
					if (ch != '=') {
						marker = '';
						continue;
					}
					marker += ch;
					if (source.endOfLine() && marker == endmarker) {
						setState(begin);
						return 'wiki-h' + depth;
					}
				}
				reset(source);
				setState(normal());
				return null;
			};
		}

		function list(source, setState) {
			// log("list(" + source.peek() + ")")
			next(source);
			next(source);
			if (source.endOfLine()) {
				setState(begin);
			} else {
				setState(normal());
			}
			return 'wiki-list';
		}

		function wrapper(prefix, suffix, style, nextState, lineEndState) {
			return function(source, setState) {
				// log("wrapper(" + source.peek() + ")");
				for (i = 0; i < prefix.length; i++) {
					next(source);
				}
				while (!source.endOfLine()) {
					if (source.lookAhead(suffix)) {
						for (i = 0; i < suffix.length; i++) {
							next(source);
						}
						if (source.endOfLine()) {
							setState(lineEndState);
						} else {
							setState(nextState);
						}
						return style;
					}
					next(source);
				}
				reset(source);
				next(source);
				setState(nextState);
				return null;
			};
		}

		function code(source, setState) {
			// log("code(" + source.peek() + ")");
			while (!source.endOfLine()) {
				var ch = source.peek();
				if (ch == '<') {
					if (source.lookAhead('</code>')) {
						next(source);
						next(source);
						next(source);
						next(source);
						next(source);
						next(source);
						next(source);
						if (source.endOfLine()) {
							setState(begin);
						} else {
							setState(normal());
						}
						return "wiki-code";
					}
				}
				next(source);
			}
			return "wiki-code";
		}

		function normal() {
			return normalUntil(null, null, begin);
		}

		function normalUntil(breakTest, breakState, lineEndState) {
			var thisState = function(source, setState) {
				// log("normal(" + source.peek() + ")");
				var prev = ' ';
				while (!source.endOfLine()) {
					var prevIsAlphaNum;
					var ch = source.peek();
					if (breakTest && breakTest(source)) {
						// log("normalBreak: "+ch);
						setState(breakState);
						return 'wiki-text';
					}
					if (/\s/.test(prev)) {
						if (ch == '<' && source.lookAhead('<code>')) {
							setState(wrapper('<code>', '</code>', 'wiki-code', thisState, lineEndState));
							return 'wiki-text';
						}
						if (ch == "'" && source.lookAhead("'''''")) {
							setState(wrapper("'''''", "'''''", 'wiki-bold-italic', thisState, lineEndState));
							return 'wiki-text';
						}
						if (ch == "'" && source.lookAhead("'''")) {
							setState(wrapper("'''", "'''", 'wiki-bold', thisState, lineEndState));
							return 'wiki-text';
						}
						if (ch == "'" && source.lookAhead("''")) {
							setState(wrapper("''", "''", 'wiki-italic', thisState, lineEndState));
							return 'wiki-text';
						}
					}
					prev = ch;
					next(source);
				}
				setState(lineEndState);
				return 'wiki-text';
			};
			return thisState;
		}

		function tableCell() {
			return function(source, setState) {
				// log("tableCell(" + source.peek() + ")");
				while (!source.endOfLine()) {
					var ch = source.peek();
					if (ch == '|') {
						setState(table);
						return 'wiki-text';
					}
					next(source);
				}
				return 'wiki-text';
			};
		}

		function table(source, setState) {
			// log("table(" + source.peek() + ")");
			if (!source.endOfLine()) {
				var ch = source.peek();
				if (ch == '|') {
					if (source.lookAhead('|}')) {
						next(source);
						next(source);
						if (source.endOfLine()) {
							setState(begin);
						} else {
							setState(normal());
						}
						return 'wiki-table';
					}
					next(source);
					return 'wiki-table';
				}
				if (ch == '!') {
					next(source);
					return 'wiki-table';
				}
				var test = function(source) {
					return source.lookAhead('||') || source.lookAhead('!!');
				};
				setState(normalUntil(test, table, table));
				// setState(tableCell());
				return null;
			}
			return 'wiki-table';
		}

		function begin(source, setState) {
			// log("begin(" + source.peek() + ")");

			if (source.indented) {
				while (!source.endOfLine())
					source.next();
				return "wiki-preformated";
			}

			var ch = source.peek();

			if (ch == '=') {
				if (ch == '=' && source.lookAhead('= ')) {
					setState(header(1));
					return null;
				}
				if (source.lookAhead('== ')) {
					setState(header(2));
					return null;
				}
				if (source.lookAhead('=== ')) {
					setState(header(3));
					return null;
				}
				if (source.lookAhead('==== ')) {
					setState(header(4));
					return null;
				}
			}

			if (ch == '<' && source.lookAhead('<code>')) {
				setState(code);
				return null;
			}

			if ((ch == '*' && source.lookAhead('* ')) || (ch == '#' && source.lookAhead('# '))) {
				setState(list);
				return null;
			}

			if (ch == '{' && source.lookAhead('{|')) {
				next(source);
				next(source);
				setState(table);
				return 'wiki-table';
			}

			setState(normal())
			return null;
		}

		return function(source, startState) {
			run++;
			return tokenizer(source, startState || begin);
		};

	})();

	function indentWiki(inBraces, inRule, base) {
		return function(nextChars) {
			return base;
		};
	}

	function parseWiki(source, basecolumn) {
		basecolumn = basecolumn || 0;
		tokens = tokenizeWiki(source);

		var iter = {
			next : function() {
				var token = tokens.next();
				var style = token.style;
				var content = token.content;

				// console.log("content: "+content);

				if (content == '\n') {
					token.indentation = indentWiki(false, false, basecolumn);
				}

				return token;
			},

			copy : function() {
				var _tokenState = tokens.state;
				return function(source) {
					tokens = tokenizeWiki(source, _tokenState);
					return iter;
				};
			}
		};
		return iter;
	}

	return {
		make : parseWiki
	};
})();
