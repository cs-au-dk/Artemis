var fn = "test.history";
if( readline.loadHistory(fn) ) {
    print("Loaded history file",fn);
} else {
    print("Couldn't load history file",fn);
}
var s = 1;
while( undefined !== (s = readline.read("Enter something (Ctrl-D quits): ")) )
{
    print("Result:",s);
}
print(""); // ensure a newline
print("Done!");
