/* Provide an implementation that satisfies the given post-condition */
method M (x0 : int) returns (x : int)
  ensures (x0 < 3 ==> x == 1) && (x0 >= 3 ==> x < x0);
  {
}

/* Provide an implementation that satisfies the given post-condition */	
method M2(a : int, b : int, c : int) returns (m : int)
  ensures (m == a || m == b || m == c);
  ensures (m <= a && m <= b && m <= c) ;
  {
}



/* Take a sequence of integers and return the unique elements of that */
/* list. There is no requirement on the ordering of the returned */
/* values. */

/* Supply meaningful post-conditions and loop invariants to verify 
   the implementation */

method Unique(a: seq<int>) returns (b: seq<int>)
{
  var index := 0;
  b := [];
  while index < |a|
  {
    if (a[index] !in b) {
      b := b + [a[index]];
    }
    assert a[index] in b;
    index := index + 1;
  }
  return b;
}


/* Given a padding character, a string, and a total length, 
   return the string padded to that length with that character. 
   If length is less than the length of the string, do nothing. */

function method max(a: int, b: int): int
{
    if a > b then a else b
}

/* Supply meaningful postconditions and loop invariants to verify 
   the implementation */

method LeftPad(c: char, n: int, s: seq<char>) returns (v: seq<char>)
  ensures |v| == max(n, |s|)

{
    
    var pad, i := max(n - |s|, 0), 0;
    v := s;
    while i < pad
    {
        v := [c] + v;
        i := i + 1;
    }
}

