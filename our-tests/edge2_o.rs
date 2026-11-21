var x = "outer";
var c = true;
if (c)
{
    var x = "inner";
    print x;
    drop x;
}
print x;
drop x;
