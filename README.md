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
We augment the collecting semantics with a symbolic collecting semantics.
In the sample evaluation, we can see both the concrete value, as well as the
symbolic value. Note that these are collecting semantics, so we see the
collection of all possible environments.

```
***program***
pc:1 (= x 1)
pc:2 (= x_lt_5 (x <. 5))
pc:3 ((while x_lt_5  
                     pc:4 Skip
                     pc:5 (= x_next (x +. 1))
                     pc:6 (= x_lt_5_next (x <. 5))
                     pc:7 (= x x_next)
                     pc:8 (= x_lt_5 x_lt_5_next)
                     pc:9 ENDWHILE)
pc:10 (= z (x +. -5))
***program output***
fromList [(id:x,6),(id:x_lt_5,0),(id:x_lt_5_next,0),(id:x_next,6),(id:z,1)]
***collecting semantics (concrete x symbol):***
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  {}
|pc:2 >>  {}
|pc:3 >>  {}
|pc:4 >>  {}
|pc:5 >>  {}
|pc:6 >>  {}
|pc:7 >>  {}
|pc:8 >>  {}
|pc:9 >>  {}
|pc:10 >>  {}
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  {}
|pc:4 >>  {}
|pc:5 >>  {}
|pc:6 >>  {}
|pc:7 >>  {}
|pc:8 >>  {}
|pc:9 >>  {}
|pc:10 >>  |z >>  (_|_, _|_)
           
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:4 >>  |x >>  (1, x )
          |x_lt_5 >>  (1,  1)
          
|pc:5 >>  |x >>  (1, x )
          |x_lt_5 >>  (1,  1)
          |x_next >>  (2, x + 1)
          
|pc:6 >>  |x >>  (1, x )
          |x_lt_5 >>  (1,  1)
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:7 >>  |x >>  (2, x + 1)
          |x_lt_5 >>  (1,  1)
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:8 >>  |x >>  (2, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:9 >>  |x >>  (2, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:10 >>  |x >>  (2, x + 1)
           |x_lt_5 >>  (1, (x  <.  5))
           |x_lt_5_next >>  (1, (x  <.  5))
           |x_next >>  (2, x + 1)
           |z >>  (-3, x + -4)
           
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  |x >>  (2, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:4 >>  |x >>  (2, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (2, x + 1)
          
|pc:5 >>  |x >>  (2, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:6 >>  |x >>  (2, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:7 >>  |x >>  (3, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:8 >>  |x >>  (3, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:9 >>  |x >>  (3, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:10 >>  |x >>  (3, x + 1)
           |x_lt_5 >>  (1, (x  <.  5))
           |x_lt_5_next >>  (1, (x  <.  5))
           |x_next >>  (3, x + 1)
           |z >>  (-2, x + -4)
           
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  |x >>  (3, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:4 >>  |x >>  (3, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (3, x + 1)
          
|pc:5 >>  |x >>  (3, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:6 >>  |x >>  (3, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:7 >>  |x >>  (4, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:8 >>  |x >>  (4, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:9 >>  |x >>  (4, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:10 >>  |x >>  (4, x + 1)
           |x_lt_5 >>  (1, (x  <.  5))
           |x_lt_5_next >>  (1, (x  <.  5))
           |x_next >>  (4, x + 1)
           |z >>  (-1, x + -4)
           
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  |x >>  (4, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:4 >>  |x >>  (4, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (4, x + 1)
          
|pc:5 >>  |x >>  (4, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:6 >>  |x >>  (4, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:7 >>  |x >>  (5, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:8 >>  |x >>  (5, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:9 >>  |x >>  (5, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:10 >>  |x >>  (5, x + 1)
           |x_lt_5 >>  (1, (x  <.  5))
           |x_lt_5_next >>  (1, (x  <.  5))
           |x_next >>  (5, x + 1)
           |z >>  (0, x + -4)
           
|pc:11 >>  {}
---
|pc:-1 >>  {}
|pc:0 >>  {}
|pc:1 >>  |x >>  (1,  1)
          
|pc:2 >>  |x >>  (1,  1)
          |x_lt_5 >>  (1,  1)
          
|pc:3 >>  |x >>  (5, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:4 >>  |x >>  (5, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (5, x + 1)
          
|pc:5 >>  |x >>  (5, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (1, (x  <.  5))
          |x_next >>  (6, x + 1)
          
|pc:6 >>  |x >>  (5, x )
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (0, (x  <.  5))
          |x_next >>  (6, x + 1)
          
|pc:7 >>  |x >>  (6, x + 1)
          |x_lt_5 >>  (1, (x  <.  5))
          |x_lt_5_next >>  (0, (x  <.  5))
          |x_next >>  (6, x + 1)
          
|pc:8 >>  |x >>  (6, x + 1)
          |x_lt_5 >>  (0, (x  <.  5))
          |x_lt_5_next >>  (0, (x  <.  5))
          |x_next >>  (6, x + 1)
          
|pc:9 >>  |x >>  (6, x + 1)
          |x_lt_5 >>  (0, (x  <.  5))
          |x_lt_5_next >>  (0, (x  <.  5))
          |x_next >>  (6, x + 1)
          
|pc:10 >>  |x >>  (6, x + 1)
           |x_lt_5 >>  (0, (x  <.  5))
           |x_lt_5_next >>  (0, (x  <.  5))
           |x_next >>  (6, x + 1)
           |z >>  (1, x + -4)
           
|pc:11 >>  {}
---
***sampling program using the abstraction:***
x_lt_5 = (1,  1)
x_lt_5_next = (T, (x  <.  5))
x = (1,  1)
x_next = (T, x + 1)
z = (T, x + -4)
```


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

## Questions about abstract interpretation:

### Multiple AI frameworks
- Consider the two frameworks of AI. One which specifies an `alpha` and a
  `gamma` in a galois connection. Given a concrete operator `f`, we _construct_
  the abstract operator `f# = alpha . f . gamma`. The second framework, which
  for each concrete operator `f`, defines an abstract operator `f#`, and also
  provides a `gamma`, under the condition that `f <= gamma(f#)`.  Given this,
  can we _recover_ `alpha` and `gamma`?  If not, how are the two approaches
  related? **Answer:** See [Antoine Mine's
  thesis](https://www-apr.lip6.fr/~mine/these/these-color.pdf), where he
  defines three styles of AI:
	- `alpha, gamma` based AI.
	- defining abstract operators `f#` for every `f` with a given `gamma`.
	- `gamma`, _partial_ `alpha` based AI.

### Questions with Antoine's thesis:
I'm trying to understand the symbolic abstract domain as constructed by Mine.

- See `Definition 6.3.4`: The definition of `gamma^symb` is confusing. I don't
  understand the type / what it returns. In particular, it seems recursively
  defined? there is a `rho` that occurs on both the LHS and the RHS.

- Similarly, theorem `6.3.1`, seems to assert that substituting bound variables
  is always sound. I don't understand what's going on there. Consider
  the case of:
  ```
  subst :: B^symb x V x B^symb -> B^symb
  rho#(X) = Z
  expr = X

  Theorem asserts:
    expr <= subst(expr, X, rho#(X))
    X <= subst(X, X, Z)
    X <= Z
  ```

  But is it true that `X <= Z`? I would have assumed that the variables
  are incomparable in the lattice. I could not find the partial order
  defined on `B^symb`. It is defined on `B^constant` at `Definition 6.3.1`.


- Also, the symbolic abstract domain's denotation operator `[[ . ]]` is not
clearly described. It is referred to in `Definition 6.3.1`, sub part `3`, but
I could not find an actual definition.

- The _meaning_ of a symbolic value is `(V -> I) -> powerset(I)` (Definition
  `6.3.1`). That is, given an environment, it provides a set of values the
  symbolic expression can take.  How is this related to the actual collecting
  semantics? That is, we are provided a concretisation function `gamma ::
  B^symb -> (V -> I) -> powerset(I)`. But `(V -> I) -> powerset(I)` is _not_
  the collecting semantics. So, **what is the proof of correctness** of this
  concretisation function `gamma`?

### Custom Collecting semantics
- When defining the collecting semantics, one can of course use the "standard"
  collecting semantics.  However, to perform analyses such as reaching
  definitions, we _modify_ the collecting semantics with extra information
  [(Lecture Notes: Widening Operators and Collecting Semantics - Jonathan
  Aldrich)](https://www.cs.cmu.edu/~aldrich/courses/15-819O-13sp/resources/widening-collecting.pdf). What kinds of modification to the collecting semantics is legal? 


### Symbolic computation as abstract interpretation
- How do we view symbolic computation as abstract interpretation?

## Links
- [Course taught at MIT (has pretty pictures for abstraction and concretization)](http://web.mit.edu/16.399/www/#notes)
