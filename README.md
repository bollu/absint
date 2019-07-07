# Absint - a simple abstract interpreter in haskell
I am following these lecture notes on performing AI for a simple bytecode
language: [absint winter school, Saint
petersburg](http://janmidtgaard.dk/aiws15/#links).

I could find no approachable uses of abstract interpretation, so I decided
to write one up for myself.

There is a TUI implementation using `brick`, a general abstract
interpretation framework (currently instantiated against presburger
arithmetic), with haskell bindings to the ISL library for presburger arithmetic.


### Open questions
- Is this _sane_? While it is possibly "mathematically correct", 
I have no idea if this is _tasteful_ since I do not know AI literature.
Critique on this would help


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
