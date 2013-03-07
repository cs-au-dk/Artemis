Object.K = function(x) {return x;};

Object.extend = function(destination, source) {
	for (var property in source) {
		destination[property] = source[property];
	}
	return destination;
};

Object.extend(Object, {
	inspect: function(object) {
		try {
			if (Object.isUndefined(object)) return 'undefined';
			if (object === null) return 'null';
			return object.inspect ? object.inspect() : String(object);
		} catch (e) {
			if (e instanceof RangeError) return '...';
			throw e;
		}
	},

	toJSON: function(object) {
		var type = typeof object;
		switch (type) {
		case 'undefined':
		case 'function':
		case 'unknown': return;
		case 'boolean': return object.toString();
		}

		if (object === null) return 'null';
		if (object.toJSON) return object.toJSON();
		if (Object.isElement(object)) return;

		var results = [];
		for (var property in object) {
			var value = Object.toJSON(object[property]);
			if (!Object.isUndefined(value))
				results.push(property.toJSON() + ': ' + value);
		}

		return '{' + results.join(', ') + '}';
	},

	toQueryString: function(object) {
		return $H(object).toQueryString();
	},

	toHTML: function(object) {
		return object && object.toHTML ? object.toHTML() : String.interpret(object);
	},

	keys: function(object) {
		var keys = [];
		for (var property in object)
			keys.push(property);
		return keys;
	},

	values: function(object) {
		var values = [];
		for (var property in object)
			values.push(object[property]);
		return values;
	},

	clone: function(object) {
		return Object.extend({ }, object);
	},

	isElement: function(object) {
		return object && object.nodeType == 1;
	},

	isArray: function(object) {
		return object != null && typeof object == "object" &&
			'splice' in object && 'join' in object;
	},

	isFunction: function(object) {
		return typeof object == "function";
	},

	isString: function(object) {
		return typeof object == "string";
	},

	isNumber: function(object) {
		return typeof object == "number";
	},

	isUndefined: function(object) {
		return typeof object == "undefined";
	}
});

Object.extend(Function.prototype, {
	argumentNames: function() {
		var names = this.toString().match(/^[\s\(]*function[^(]*\((.*?)\)/)[1].split(",").invoke("strip");
		return names.length == 1 && !names[0] ? [] : names;
	},

	bind: function() {
		if (arguments.length < 2 && Object.isUndefined(arguments[0])) return this;
		var __method = this, args = $A(arguments), object = args.shift();
		return function() {
			return __method.apply(object, args.concat($A(arguments)));
		};
	},

	bindAsEventListener: function() {
		var __method = this, args = $A(arguments), object = args.shift();
		return function(event) {
			return __method.apply(object, [event || window.event].concat(args));
		};
	},

	curry: function() {
		if (!arguments.length) return this;
		var __method = this, args = $A(arguments);
		return function() {
			return __method.apply(this, args.concat($A(arguments)));
		};
	},

	delay: function() {
		var __method = this, args = $A(arguments), timeout = args.shift() * 1000;
		return window.setTimeout(function() {
			return __method.apply(__method, args);
		}, timeout);
	},

	wrap: function(wrapper) {
		var __method = this;
		return function() {
			return wrapper.apply(this, [__method.bind(this)].concat($A(arguments)));
		};
	},

	methodize: function() {
		if (this._methodized) return this._methodized;
		var __method = this;
		return this._methodized = function() {
			return __method.apply(null, [this].concat($A(arguments)));
		};
	}
});

Object.extend = function(destination, source) {
	for (var property in source)
		destination[property] = source[property];
	return destination;
};

Object.extend(Object, {
	inspect: function(object) {
		try {
			if (Object.isUndefined(object)) return 'undefined';
			if (object === null) return 'null';
			return object.inspect ? object.inspect() : String(object);
		} catch (e) {
			if (e instanceof RangeError) return '...';
			throw e;
		}
	},

	toJSON: function(object) {
		var type = typeof object;
		switch (type) {
		case 'undefined':
		case 'function':
		case 'unknown': return;
		case 'boolean': return object.toString();
		}

		if (object === null) return 'null';
		if (object.toJSON) return object.toJSON();
		if (Object.isElement(object)) return;

		var results = [];
		for (var property in object) {
			var value = Object.toJSON(object[property]);
			if (!Object.isUndefined(value))
				results.push(property.toJSON() + ': ' + value);
		}

		return '{' + results.join(', ') + '}';
	},

	toQueryString: function(object) {
		return $H(object).toQueryString();
	},

	toHTML: function(object) {
		return object && object.toHTML ? object.toHTML() : String.interpret(object);
	},

	keys: function(object) {
		var keys = [];
		for (var property in object)
			keys.push(property);
		return keys;
	},

	values: function(object) {
		var values = [];
		for (var property in object)
			values.push(object[property]);
		return values;
	},

	clone: function(object) {
		return Object.extend({ }, object);
	},

	isElement: function(object) {
		return object && object.nodeType == 1;
	},

	isArray: function(object) {
		return object != null && typeof object == "object" &&
			'splice' in object && 'join' in object;
	},

	isHash: function(object) {
		return object instanceof Hash;
	},

	isFunction: function(object) {
		return typeof object == "function";
	},

	isString: function(object) {
		return typeof object == "string";
	},

	isNumber: function(object) {
		return typeof object == "number";
	},

	isUndefined: function(object) {
		return typeof object == "undefined";
	}
});

Object.extend(Function.prototype, {
	argumentNames: function() {
		var names = this.toString().match(/^[\s\(]*function[^(]*\((.*?)\)/)[1].split(",").invoke("strip");
		return names.length == 1 && !names[0] ? [] : names;
	},

	bind: function() {
		if (arguments.length < 2 && Object.isUndefined(arguments[0])) return this;
		var __method = this, args = $A(arguments), object = args.shift();
		return function() {
			return __method.apply(object, args.concat($A(arguments)));
		};
	},

	bindAsEventListener: function() {
		var __method = this, args = $A(arguments), object = args.shift();
		return function(event) {
			return __method.apply(object, [event || window.event].concat(args));
		};
	},

	curry: function() {
		if (!arguments.length) return this;
		var __method = this, args = $A(arguments);
		return function() {
			return __method.apply(this, args.concat($A(arguments)));
		};
	},

	delay: function() {
		var __method = this, args = $A(arguments), timeout = args.shift() * 1000;
		return window.setTimeout(function() {
			return __method.apply(__method, args);
		}, timeout);
	},

	wrap: function(wrapper) {
		var __method = this;
		return function() {
			return wrapper.apply(this, [__method.bind(this)].concat($A(arguments)));
		};
	},

	methodize: function() {
		if (this._methodized) return this._methodized;
		var __method = this;
		return this._methodized = function() {
			return __method.apply(null, [this].concat($A(arguments)));
		};
	}
});

var $break = { };

var Enumerable = {
	each: function(iterator, context) {
		var index = 0;
		try {
			this._each(function(value) {
				iterator(value, index++);
			});
		} catch (e) {
			if (e != $break) throw e;
		}
		return this;
	},

	eachSlice: function(number, iterator, context) {
		var index = -number, slices = [], array = this.toArray();
		while ((index += number) < array.length)
			slices.push(array.slice(index, index+number));
		return slices.collect(iterator, context);
	},

	all: function(iterator, context) {
		var result = true;
		this.each(function(value, index) {
			result = result && !!iterator(value, index);
			if (!result) throw $break;
		});
		return result;
	},

	groupBy: function(iterator, context) {
		var result = {};
		this.each(function(value, index) {
            var key = iterator(value, index);
            if (!result[key]) result[key] = [];
            result[key].append(value);
        });
        return result;
    },

	any: function(iterator, context) {
		var result = false;
		this.each(function(value, index) {
			if (result = !!iterator(value, index))
				throw $break;
	    });
		return result;
	},

	collect: function(iterator, context) {
		var results = [];
		this.each(function(value, index) {
					  results.push(iterator(value, index));
				  });
		return results;
	},

	detect: function(iterator, context) {
		var result;
		this.each(function(value, index) {
			if (iterator(value, index)) {
				result = value;
				throw $break;
			}
		});
		return result;
	},

	findAll: function(iterator, context) {
		var results = [];
		this.each(function(value, index) {
			if (iterator(value, index))
				results.push(value);
	    });
		return results;
	},

	grep: function(filter, iterator, context) {
		var results = [];

		if (Object.isString(filter))
			filter = new RegExp(filter);

		this.each(function(value, index) {
			if (filter.match(value))
				results.push(iterator(value, index));
	    });
		return results;
	},

	include: function(object) {
		if (Object.isFunction(this.indexOf))
			if (this.indexOf(object) != -1) return true;

		var found = false;
		this.each(function(value) {
			if (value == object) {
				found = true;
				throw $break;
			}
		});
		return found;
	},

	inGroupsOf: function(number, fillWith) {
		fillWith = Object.isUndefined(fillWith) ? null : fillWith;
		return this.eachSlice(number, function(slice) {
			while(slice.length < number) slice.push(fillWith);
				return slice;
		});
	},

	inject: function(memo, iterator, context) {
		this.each(function(value, index) {
		    memo = iterator(memo, value, index);
		});
		return memo;
	},

	invoke: function(method) {
		var args = $A(arguments).slice(1);
		return this.map(function(value) {
			return value[method].apply(value, args);
		});
	},

	max: function(iterator, context) {
		var result;
		this.each(function(value, index) {
			value = iterator(value, index);
		    if (result == null || value >= result)
		        result = value;
		});
		return result;
	},

	min: function(iterator, context) {
		var result;
		this.each(function(value, index) {
					  value = iterator(value, index);
					  if (result == null || value < result)
						  result = value;
				  });
		return result;
	},

	partition: function(iterator, context) {
		var trues = [], falses = [];
		this.each(function(value, index) {
					  (iterator(value, index) ?
					   trues : falses).push(value);
				  });
		return [trues, falses];
	},

	pluck: function(property) {
		var results = [];
		this.each(function(value) {
			results.push(value[property]);
		});
		return results;
	},

	reject: function(iterator, context) {
		var results = [];
		this.each(function(value, index) {
			if (!iterator(value, index))
				results.push(value);
		});
		return results;
	},

	sortBy: function(iterator, context) {
		return this.map(function(value, index) {
			return {value: value, criteria: iterator(value, index)};
		}).sort(function(left, right) {
			var a = left.criteria, b = right.criteria;
			return a < b ? -1 : a > b ? 1 : 0;
		}).pluck('value');
	},

	toArray: function() {
		return this.map();
	},

	zip: function() {
		var iterator = Object.K, args = $A(arguments);
		if (Object.isFunction(args.last()))
			iterator = args.pop();

		var collections = [this].concat(args).map($A);
		return this.map(function(value, index) {
			return iterator(collections.pluck(index));
		});
	},

	size: function() {
		return this.toArray().length;
	},

	inspect: function() {
		return '#<Enumerable:' + this.toArray().inspect() + '>';
	}
};

Object.extend(Enumerable, {
	map:     Enumerable.collect,
	find:    Enumerable.detect,
	select:  Enumerable.findAll,
	filter:  Enumerable.findAll,
	member:  Enumerable.include,
	entries: Enumerable.toArray,
	every:   Enumerable.all,
	some:    Enumerable.any
});

function $A(iterable) {
	if (!iterable) return [];
	if (iterable.toArray) return iterable.toArray();
	var length = iterable.length || 0, results = new Array(length);
	while (length--) results[length] = iterable[length];
	return results;
}

Array.from = $A;

Object.extend(Array.prototype, Enumerable);

if (!Array.prototype._reverse) Array.prototype._reverse = Array.prototype.reverse;

Object.extend(Array.prototype, {
	_each: function(iterator) {
		for (var i = 0, length = this.length; i < length; i++)
			iterator(this[i]);
	},

	clear: function() {
		this.length = 0;
		return this;
	},

	first: function() {
		return this[0];
	},

	last: function() {
		return this[this.length - 1];
	},

	compact: function() {
		return this.select(function(value) {
			return value != null;
		});
	},

	flatten: function() {
		return this.inject([], function(array, value) {
			return array.concat(Object.isArray(value) ? value.flatten() : [value]);
		});
	},

	without: function() {
		var values = $A(arguments);
		return this.select(function(value) {
			return !values.include(value);
		});
	},

	reverse: function(inline) {
		return (inline !== false ? this : this.toArray())._reverse();
	},

	reduce: function() {
		return this.length > 1 ? this : this[0];
	},

	uniq: function(sorted) {
		return this.inject([], function(array, value, index) {
			if (0 == index || (sorted ? array.last() != value : !array.include(value)))
				array.push(value);
			return array;
		});
	},

	intersect: function(array) {
		return this.uniq().findAll(function(item) {
			return array.detect(function(value) { return item === value });
		});
	},

	clone: function() {
		return [].concat(this);
	},

	size: function() {
		return this.length;
	},

	inspect: function() {
		return '[' + this.map(Object.inspect).join(', ') + ']';
	},

	toJSON: function() {
		var results = [];
		this.each(function(object) {
			var value = Object.toJSON(object);
			if (!Object.isUndefined(value)) results.push(value);
		});
		return '[' + results.join(', ') + ']';
	}
});

// use native browser JS 1.6 implementation if available
if (Object.isFunction(Array.prototype.forEach))
	Array.prototype._each = Array.prototype.forEach;

if (!Array.prototype.indexOf) Array.prototype.indexOf = function(item, i) {
	i || (i = 0);
	var length = this.length;
	if (i < 0) i = length + i;
	for (; i < length; i++)
		if (this[i] === item) return i;
	return -1;
};

if (!Array.prototype.lastIndexOf) Array.prototype.lastIndexOf = function(item, i) {
	i = isNaN(i) ? this.length : (i < 0 ? this.length + i : i) + 1;
	var n = this.slice(0, i).reverse().indexOf(item);
	return (n < 0) ? n : i - n - 1;
};

Array.prototype.toArray = Array.prototype.clone;

Object.extend(Number.prototype, {
  toColorPart: function() {
    return this.toPaddedString(2, 16);
  },

  succ: function() {
    return this + 1;
  },

  times: function(iterator) {
    $R(0, this, true).each(iterator);
    return this;
  },

  toPaddedString: function(length, radix) {
    var string = this.toString(radix || 10);
    return '0'.times(length - string.length) + string;
  },

  toJSON: function() {
    return isFinite(this) ? this.toString() : 'null';
  }
});

var $R = function(start, end, exclusive) {
	var range = {};

	Object.extend(range, Enumerable);

	range._each = function(iterator) {
		var value = start;
		while (range.include(value)) {
			iterator(value);
			value = value.succ();
		}
	};

	range.include = function(value) {
		if (value < start)
			return false;
		if (exclusive)
			return value < end;
		return value <= end;
	};

	return range;
};

