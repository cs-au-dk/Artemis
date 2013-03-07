// a simple cache ---------------------

// give it a function that computes a value
// it will compute the value the first time it is called,
// and then cache it.  It uses the cached value
// until expire is called, which triggers the cache
// to be recomputed on its next access.
var cache = function(find) {
	var value = null;

	var that = function() {
		if (value === null) {
			value = find();
		}
		return value;
	};

    that.expiring = function() {};
	that.expire = function() {
		value = null;
        that.expiring();
	};

	return that;
};


// model of dependent values --------------------

// a linkage is a single value which can be watched for changes.
var linkage = function() {
	var value = arguments.length === 0 ? null : arguments[0];
	var index = 1;
	var keys = [];
	var observers = [];

	// if called with no arguments, returns its value
	// a single argument sets the value
	var that = function() {
		if (arguments.length === 0) {
			return value;
		} else {
			value = arguments[0];

			// trigger observers
			if (keys.length > 0) {
				for (var key=0; key < keys.length; key++) {
					observers[keys[key]](value);
				}
			}

			return value;
		}
	};

	// watch takes a function of one argument
	// which is called whenever this value changes
	that.watch = function(observer) {
		var id = index;
		observers[id] = observer;
		keys.push(id);
		index++;

		return id;
	};

	// given the id returned from a previous watch() call,
	// disables that observer
	that.unwatch = function(id) {
		keys.splice(keys.indexOf(id), 1);
	};

	return that;
};


Object.prototype.access = function(entry) {
	if (entry) {
		var path = entry.split('.');
		var component = path.shift();
		var parts = component.match(/([^\(]+)\(([^\)]*)\)/);
		var found = parts === null ? this[component] : this[parts[1]](parts[2]);

		return found.access(path.join('.'));
	} else {
		return this;
	}
};