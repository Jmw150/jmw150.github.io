
/*

- Dafny is a programming language, verifier, and compiler all rolled into one.
- Designed from the ground-up with static verification in mind.
- Uses a theorem prover (SMT solver) to automatically prove correctness.
- But, it may not always be possible to discharge a proof.  When this happens, 
  the user will need to provide additional annotations.


Dafny makes it easier to write correct code
--------------------------------------------
	 
Correctness means two things:

     ▶ No runtime errors: null deref., div. by 0, index o.o.b, ...
     ▶ Program does what you intended
     ▶ Terminates (when applicable)

Your intentions are captured with a *specification*


What does correctness mean in the Dafny context?

- Correctness is defined with respect to specifications (pre- and post-conditions)
- It may reflect base-level semantic properties (no runtime errors (e.g., 
  divide-by-zero, null pointer dereferences, etc.), but it can also identify 
  higher-level application-specific properties. 

- Specifications are meant to capture salient behavior of an application, eliding
  issues of efficiency and low-level representation.

          forall k:int :: 0 <= k < a.Length ==> 0 < a[k]

- Specifications in Dafny can be arbitrarily sophisticated.
  
- We can think of Dafny as being two smaller languages rolled into one:

   - An imperative core that has methods, loops, arrays, if statements... and
     other features found in realistic programming languages.  This core can
     be compiled and executed.

   - A pure (functional) specification language that supports functions, sets,
     predicates, algebraic datatypes, etc.  This language is used by the prover
     but is not compiled.




                         /------------------ .Net Compiler --> Executable
                        /C# code
                       /
       Dafny Code     /
   ------------------>
                      \
                       \
                        \
                        -------------------- Dafny Verifier --> Verification result
                                                  |
                                                  |
                                                Boogie
                                                  |
                                                  |
                                                Z3 SMT



*/

/* Methods */

method MultipleReturns(x: int, y: int) returns (more: int, less: int) {
  more := x + y;
  less := x - y;
}

/* Pre- and Post-condition */

method MultipleReturnsSpec(x: int, y: int) returns (more: int, less: int) 
  	ensures less < x
		ensures x < more
{
  more := x + y;
  less := x - y;
}

method MultipleReturnsSpecFixA(x: int, y: int) returns (more: int, less: int)
	  requires y > 0
  	ensures less < x
		ensures x < more
{
  more := x + y;
  less := x - y;
}

method Max (a : int, b : int) returns (c : int)
	ensures (a <= c && b <= c) && (b == c || a == c)
{
	if (a < b) {
		c := b;
	}
	else { c := a; }
	}

/* assertions */	

method Abs(x: int) returns (r: int) 
  ensures r >= 0
	{
    if (x < 0)
      { return -x; }
    else
      { return x; }
  }

method TestBroken() {
	var x := Abs(3);
	assert (x == 3);
}

method TestAbs()
{
   var v := Abs(3);
   assert 0 <= v;
}

method Test() {
	var x := Abs(-3);
	assert (x > 0);
}

method AbsFixed(x: int)	returns (y: int)
  ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
  if (x < 0) { return -x; }
     else { return x; }
}

method TestFixed() {
	var x := AbsFixed(-3);
	assert (x > 0);
}

method TestFixedA() {
	var x := AbsFixed(-3);
	assert (x == 3);
}


method AbsFixedA(x: int)	returns (y: int)
	ensures 0 <= y && ( y == x || y == -x)
{
  if (x < 0) { return -x; }
     else { return x; }
}


method AbsFixedEx1(x: int)	returns (y: int)
	requires x == -1
	ensures 0 <= y && ( y == x || y == -x)
{
  y := x + 2;
}


method AbsFixedEx2(x: int)	returns (y: int)
	requires false
	ensures 0 <= y && ( y == x || y == -x)
{
  y := x + 1;
}


/* Functions */

function abs(x: int): int
 {
  if x < 0 then -x else x
}


method TestFixedB() {
	var x := AbsFixed(-3);
	assert x == abs(-3);
}

function max(a : int, b : int) : int {
	if (a <= b) then b else a
}

method TestMax() {
	var m := Max(3,4);
	assert m == max(3,4);
}


method MaxFixed (a : int, b : int) returns (c : int)
	ensures (a <= b ==> c == b) || (b < a ==> c == a)
{
	if (a < b) {
		c := b;
	}
	else { c := a; }
	}

method TestMaxA() {
	var m := MaxFixed(3,4);
	assert m == max(3,4);
}

	
function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
            fib(n - 1) + fib(n - 2)
}


/* Loops */

method loopExCheck (n : nat)
{
	var i : int := 0;
	while (i < n)
		invariant 0 <= i
		{ 
			i := i + 1;
	}
	assert i == n;
}


method loopExCheckFixed (n : nat)
{
	var i : int := 0;
	while (i < n)
		invariant 0 <= i <= n
		{ 
			i := i + 1;
	}
	assert i == n;
}


method loopExCheckFixedA (n : nat)
{
	var i : int := 0;
	while (i < n)
		invariant 0 <= i <= n + 2
		{ 
			i := i + 1;
	}
	assert i == n;
}



method ComputeFibBroken (n: nat) returns (x: nat)
	ensures x == fib(n);
{
  var i := 0;
	x := 0;
  var y := 1;
	while (i < n) {
    x, y := y, x+y;
		i := i + 1;
	}
}	


method ComputeFib (n: nat) returns (y: nat)
	ensures y == fib(n);
{
	if (n == 0) { return 0; }

  var i := 1;
  var x := 0;
  y := 1;

	while (i < n) 
		invariant 0 < i <= n 
   invariant x == fib (i - 1) 
    invariant y == fib (i)
		
		{
    x, y := y, x+y;
		i := i + 1;
	}
}	

method ComputeFibA (n : nat) returns (b : nat)
	ensures b == fib(n);
{
	b := 0;
	var c := 1;
	var i := 0;

	while (i < n)
		invariant 0 <= i <= n
		invariant b == fib (i)
		invariant c == fib (i + 1)
	{
		b, c := c, c + b;
		i := i + 1;
	}
}

/* decrease annotation */

method m()
{
   var i, n := 0, 20;
   while i < n
      invariant 0 <= i <= n
      decreases n - i
   {
      i := i + 1;
   }
}


method mBroken()
{
   var i, n := 0, 20;
   while i != n
      decreases n - i
   {
      i := i + 1;
   }
}

method mFixed()
{
   var i, n := 0, 20;
   while i != n
		  invariant i <= n
      decreases n - i
   {
      i := i + 1;
   }
}


/* Searching for Elements in an Array */

method FindTrivial(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
{
   index := -1;
}

method FindWithoutInvariant(a: array<int>, key: int)
	returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
	while (index < a. Length) {
		if (a[index] == key)
   		{ return index;}
		index := index + 1;
	}
	index := -1;
}

method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
	while (index < a. Length)
		invariant 0 <= index <= a.Length
		invariant forall j :: 0 <= j < index ==> a[j] != key
  {
		if (a[index] == key)
   	{ return index;}
				index := index + 1;		

	}
	index := -1;
}

method FindMax(a: array<int>) returns (j: int) 
  ensures a.Length > 0 ==> 0 <= j < a.Length &&
	        forall k :: 0 <= k < a.Length ==> a[k] <= a[j]
  requires a.Length > 0 
{
	var i := 1;
	j := 0;
 	
	while (i < a.Length)
		invariant 0 <= j < i
		invariant 0 < i <= a.Length 
		invariant forall m :: 0 <= m < i ==> a[m] <= a[j]
		decreases (a.Length - i) {
    
		if a[i] > a[j]
      { j := i; }
		i := i + 1;
	}
}

/*  Binary Search */

predicate sorted(a: array?<int>)
  requires a != null
	reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

predicate sortedDistinct(a: array<int>)
	reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k] 
}

predicate sortedNull(a: array?<int>)
	reads a
{
  (a == null ==> false) &&
		forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k] 
}


predicate sortedArray(a : array<int>)
	reads a
{
  forall j,k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array?<int>, key: int) returns (index: int)
  requires a != null && sortedArray(a)
  ensures 0 <= index ==> index < a.Length && a[index] == key 
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key 
{
   var low, high := 0, a.Length;
   while low < high
     invariant 0 <= low <= high <= a.Length
     invariant forall i ::  0 <= i < a.Length && !(low <= i < high) ==> a[i] != key 
   {
      var mid := (low + high) / 2;
      if a[mid] < key
      {
         low := mid + 1;
      }
      else if key < a[mid]
      {
         high := mid;
      }
      else
      {
         return mid;
      }
   }
   return -1; 
}

			
/* Lemmas */

method searchForZeroOpt (a: array<int>) returns (index : int)
	 /* all elements non-negative */
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]

 /* each successive element decreases by at most one from its predecessor */
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]

  ensures 0 <= index < a.Length ==> a[index] == 0	&&
	        forall k :: 0 <= k < index ==> a[k] != 0  
{
   index := 0;
   while index < a.Length
      invariant 0 <= index 
      invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
   {
      if a[index] == 0 { return; }
      index := index + a[index];
   }
   index := -1;
}


method searchForZero (a: array<int>) returns (index : int)
	/* all elements non-negative */
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]

 /* each successive element decreases by at most one from its predecessor */
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]

  ensures 0 <= index < a.Length ==> a[index] == 0	&&
	        forall k :: 0 <= k < index ==> a[k] != 0
{

   index := 0;
   while index < a.Length
      invariant 0 <= index
      invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
   {
    if a[index] == 0 { return; }
		  SkippingLemma(a,index);
      index := index + a[index];
   }
   index := -1;		
}



lemma SkippingLemma(a : array<int>, j : int)
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
  	var i := j;
		while i < j + a[j] && i < a.Length
      invariant i < a.Length ==> a[j] - (i-j) <= a[i]
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
   {
      i := i + 1;
   }
}

/* count zeros */

function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   (if a[0] then 1 else 0) + count(a[1..])
}


method TestCount()
{
   assert count([]) == 0;
   assert count([true]) == 1;
   assert count([false]) == 0;
   assert count([true, true]) == 2;
}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
   ensures count(a + b) == count(a) + count(b)
{
   if a == []
   {
      assert a + b == b;
   }
   else
   {
      DistributiveLemma(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
   }
}

/* Paths in Directed Graphs */

class Node
{
   var next: seq<Node>
}

predicate closed(graph: set<Node>)
   reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph
		&& i.next[k] != i
}

predicate path(p: seq<Node>, graph: set<Node>)
   requires closed(graph) && 0 < |p|
   reads graph
{
   p[0] in graph &&
   (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
      path(p[1..], graph)) // and the rest of the sequence is a valid
}

predicate pathSpecific(p: seq<Node>, start: Node,
	                     end: Node, graph: set<Node>)
   requires closed(graph)
   reads graph
{
   0 < |p| && // path is nonempty
   start == p[0] && end == p[|p|-1] && // it starts and ends correctly
   path(p, graph) // and it is a valid path
}

lemma ClosedLemma(subgraph: set<Node>, root: Node,
	                goal: Node, graph: set<Node>)
   requires closed(subgraph) && closed(graph) && subgraph <= graph
   requires root in subgraph && goal in graph - subgraph
   ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))

{
   forall p {
      DisproofLemma(p, subgraph, root, goal, graph);
	 }
}

lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
   requires closed(subgraph) && closed(graph) && subgraph <= graph
   requires root in subgraph && goal in graph - subgraph
   ensures !pathSpecific(p, root, goal, graph)

	{
   if 1 < |p| && p[0] == root && p[|p|-1] == goal {
      if p[1] in p[0].next {
         DisproofLemma(p[1..], subgraph, p[1], goal, graph);
      }
   }
}

/* Bubble sort */

method bubbleSortA (a : array?<int>)
	requires a != null
	requires a.Length > 1
	modifies a
	ensures sortedArray(a) {

		var i := 1;
		while i < a.Length
			invariant 1 <= i <= a.Length;
			invariant forall k,j :: 0 <= k < j < i ==> a[k] <= a[j];
		{
			assume forall k,j :: 0 <= k < j < i + 1 ==> a[k] <= a[j];
			i := i + 1;
		}
}

predicate sortedBetween (a: array<int>, lo: int , hi: int)
	requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall i,j :: (lo <= i < j < hi) ==> a[i] <= a[j]
}

predicate sortedBS (a: array?<int>)
	requires a != null
  reads a
 {
   sortedBetween (a,0,a.Length )
 }

method bubbleSortB (a: array?<int>)
	requires a != null
  modifies a
  ensures sortedArray(a)
  {
     if a.Length > 1 {
        var i := 1;
        while i < a.Length
          invariant 1 <= i <= a.Length;
					invariant sortedBetween(a,0,i); {
             // bubbleStep(a,i);
             assume sortedBetween (a ,0 , i +1);
						 i:= i+1;
        }
     }
} 

method bubbleStepA (a: array?<int> , i:int)
  requires a != null
	requires 0 <= i < a.Length
	requires sortedBetween(a,0,i)
	modifies a
  ensures sortedBetween (a ,0 , i +1)

{
	var j := i;
	while (j > 0 && a[j-1] > a[j])
		invariant 0 <= j <= i;
		invariant sortedBetween(a,0,j)
    invariant sortedBetween(a,j,i+1);

	{
		a[j-1],a[j] := a[j],a[j-1];
		j := j - 1;
	}
}

method bubbleStepB (a: array?<int> , i:int)
  requires a != null
  modifies a

	requires 0 <= i < a.Length
	requires sortedBetween(a,0,i)
  ensures sortedBetween (a,0,i+1)

{
	var j := i;
	while (j > 0 && a[j-1] > a[j])
		invariant 0 <= j <= i;
		invariant sortedBetween(a,0,j);
		invariant sortedBetween(a,j,i+1);
		invariant 1 < j+1 <= i ==> a[j-1] <= a[j+1]

	{
		a[j-1],a[j] := a[j],a[j-1];
		j := j - 1;
	}
}
