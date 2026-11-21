var x = "hello";
drop x;
var n = 0;
input n;
var k = 5;
if (n < k)
{
    var y = "world";
    x = y;
    print x;
    drop x;
}
