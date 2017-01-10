var x = artemisInputString('x');
var y = artemisInputInteger('y');
var z = artemisInputBoolean('z');

if (x == "testme") {
    alert("String '" + x + "' is OK");
} else {
    alert("String '" + x + "' is not valid.");
}

if (y > 10) {
    alert("Int '" + y + "' is OK");
} else {
    alert("Int '" + y + "' is not valid.");
}

if (z) {
    alert("Bool '" + z + "' is OK");
} else {
    alert("Bool '" + z + "' is not valid.");
}