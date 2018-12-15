# Absint - a simple abstract interpreter in haskell
I am following these lecture notes on performing AI for a simple bytecode
language: [absint winter school, Saint
petersburg](http://janmidtgaard.dk/aiws15/#links).

I could find no approachable uses of abstract interpretation, so I decided
to write one up for myself.

## Idea

We define our piecewise affine approximation as an abstract interpretation over a weird 
style of collecting semantics. We motivate this with respect to an example:

```i
pc:1 (= x 1)
pc:2 (= x_lt_5 (<. x 5))
pc:3 ((while x_lt_5  
                     pc:4 Skip
                     pc:5 (= x (+. x 1))
                     pc:6 (= x_lt_5 (<. x 5))
                     pc:7 ENDWHILE)
pc:8 (= z (+. x -5))
```

We are interested in computing affine functions for each of the variables `x`, `y`, and `z`. We proceed to describe
a special type of collecting semantics, on which we perform abstract interpretation to construct our piecewise
affine approximation

### Concrete collecting semantics
Consider the concrete collecting semantics, which of this program looks like so:

The output is read as follows: We print out a _collection_ of environments. Each environment
maps a program counter `pc` to the values of variables __after the instruction at that `pc` has executed__.

```
***collecting semantics (concrete):***
pc:-1 -> []
pc:0 -> []
pc:1 -> []
pc:2 -> []
pc:3 -> []
pc:4 -> []
pc:5 -> []
pc:6 -> []
pc:7 -> []
pc:8 -> []
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,1)]
pc:2 -> [(id:x,1),(id:x_lt_5,1)]
pc:3 -> []
pc:4 -> []
pc:5 -> []
pc:6 -> []
pc:7 -> []
pc:8 -> []
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,1)]
pc:2 -> [(id:x,1),(id:x_lt_5,1)]
pc:3 -> [(id:x,1),(id:x_lt_5,1)]
pc:4 -> [(id:x,1),(id:x_lt_5,1)]
pc:5 -> [(id:x,2),(id:x_lt_5,1)]
pc:6 -> [(id:x,2),(id:x_lt_5,1)]
pc:7 -> [(id:x,2),(id:x_lt_5,1)]
pc:8 -> [(id:x,2),(id:x_lt_5,1),(id:z,-3)]
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,1)]
pc:2 -> [(id:x,1),(id:x_lt_5,1)]
pc:3 -> [(id:x,2),(id:x_lt_5,1)]
pc:4 -> [(id:x,2),(id:x_lt_5,1)]
pc:5 -> [(id:x,3),(id:x_lt_5,1)]
pc:6 -> [(id:x,3),(id:x_lt_5,1)]
pc:7 -> [(id:x,3),(id:x_lt_5,1)]
pc:8 -> [(id:x,3),(id:x_lt_5,1),(id:z,-2)]
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,1)]
pc:2 -> [(id:x,1),(id:x_lt_5,1)]
pc:3 -> [(id:x,3),(id:x_lt_5,1)]
pc:4 -> [(id:x,3),(id:x_lt_5,1)]
pc:5 -> [(id:x,4),(id:x_lt_5,1)]
pc:6 -> [(id:x,4),(id:x_lt_5,1)]
pc:7 -> [(id:x,4),(id:x_lt_5,1)]
pc:8 -> [(id:x,4),(id:x_lt_5,1),(id:z,-1)]
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,1)]
pc:2 -> [(id:x,1),(id:x_lt_5,1)]
pc:3 -> [(id:x,4),(id:x_lt_5,1)]
pc:4 -> [(id:x,4),(id:x_lt_5,1)]
pc:5 -> [(id:x,5),(id:x_lt_5,1)]
pc:6 -> [(id:x,5),(id:x_lt_5,0)]
pc:7 -> [(id:x,5),(id:x_lt_5,0)]
pc:8 -> [(id:x,5),(id:x_lt_5,0),(id:z,0)]
pc:9 -> []
---
```


#### Why this semantics is insufficient (I think so, @grosser, @laure, please comment)

In this semantics, what we are given is the _evaluation_ of a program at
different program points. Note that computing this semantics is in itself undecidable.

However, given an oracle that _does_ compute this semantics, we can still not
produce a piecewise linear function, since to do so, we may have to examine the trace
of a potentially infinite program. 

However, this forms a useful stepping stone for semantics that is actually useful to us.

### Symbolic collecting semantics
We now define a family of collecting semantics, that is parametrized by an _opaque list_.
These collecting semantics evaluate concretely, except when they are told to switch to
symbolic variants of variables, at which point we perform symbolic execution.

For example, the same program as shown above parametrized by

```hs
-- From PC 4, treat the variable "x" as a symbol
-- We choose `PC 4` since that is where the loop starts
pToOpaqify :: OpaqueVals                                                                                                                              
pToOpaqify = OpaqueVals (M.fromList $ [(PC 4, [Id "x"])])                                                                                             
```

provides the collecting semantics:

```
pc:-1 -> []
pc:0 -> []
pc:1 -> []
pc:2 -> []
pc:3 -> []
pc:4 -> []
pc:5 -> []
pc:6 -> []
pc:7 -> []
pc:8 -> []
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,sym-1)]
pc:2 -> [(id:x,sym-1),(id:x_lt_5,sym-1)]
pc:3 -> []
pc:4 -> []
pc:5 -> []
pc:6 -> []
pc:7 -> []
pc:8 -> []
pc:9 -> []
---
pc:-1 -> []
pc:0 -> []
pc:1 -> [(id:x,sym-1)]
pc:2 -> [(id:x,sym-1),(id:x_lt_5,sym-1)]
pc:3 -> [(id:x,sym-1),(id:x_lt_5,sym-1)]
pc:4 -> [(id:x,sym-id:x),(id:x_lt_5,sym-1)]
pc:5 -> [(id:x,(op:+ sym-id:x sym-1)),(id:x_lt_5,sym-1)]
pc:6 -> [(id:x,(op:+ sym-id:x sym-1)),(id:x_lt_5,(op:< (op:+ sym-id:x sym-1) sym-5))]
pc:7 -> [(id:x,(op:+ sym-id:x sym-1)),(id:x_lt_5,(op:< (op:+ sym-id:x sym-1) sym-5))]
pc:8 -> [(id:x,(op:+ sym-id:x sym-1)),(id:x_lt_5,(op:< (op:+ sym-id:x sym-1) sym-5)),
          (id:z,(op:+ (op:+ sym-id:x sym-1) sym--5))]
pc:9 -> []
---
```

We reach fixpoint quickly. In particular, we are only able to execute one iteration of the loop,
since we are unable to evaluate the condition `x_lt_5`, which is now _symbolic_:
```
pc:8 -> [..., (id:x_lt_5,(op:< (op:+ sym-id:x sym-1) sym-5)), ...]
that is,
x_lt_5 = x + 1 < 5
```

However, the upshot is that we now have a _symbolic_ representation of the value of `x` along the backedge:

```
pc:8 -> [(id:x,(op:+ sym-id:x sym-1)), ...]
that is,
x = x + 1
```

From this symbolic representation, we can _now perform abstract interpretation_ to keep the piecewise affine
values.

### Open questions
- Is this _sane_? While it is possibly "mathematically correct", 
I have no idea if this is _tasteful_ since I do not know AI literature. Critique on this would help

- The "parametrize the symbolic collecting semantics" thing is super weird in my eyes, because
to actually perform the final analysis, we will need to repeatedly perform AI over different
parametrizations of our semantics.

Eg, if we have:

```
while x < 5 {
  while y < 10 { 
    y = y + 5
  }
  x = x + 1
}
```

We will need to first make `x` opaque, evaluate it, then make `y` opaque, evaluate it, etc.
Is this sane?

### TL;DR
construct a weird form of collecting semantics over which we can perform abstract interpretation.
This allows us to talk about the things we do:
- Making loop variables `opaque` and then accelerating them
- Actually identifying the values along the backedge the way we do
- A collecting semantics that is of use to us

## Links
- [Course taught at MIT (has pretty pictures for abstraction and concretization)](http://web.mit.edu/16.399/www/#notes)
