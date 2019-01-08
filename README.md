# Ane-Language

Ane is a tool-language to analyze lambda terms that's ensure a real time manipulation of lambda terms.
Ane uses total untyped lambda calculus, however you can use typed operations therefore terms can be easily changed and makes assumptions.

For example you need to know if two terms computes in the same way:
```
Simply Example ::
Definition : ret.
Term ret : λx -> λi -> x.
Term retTwo : λx -> λi -> ((λx -> x) x).
Term Atom : λatom -> *.
End_Terms.

Beta-Reduction ret in x in Atom.
Beta-Reduction retTwo in x in Atom.
Apply ret.
Apply retTwo.
Equal ret and retTwo.
Show.
Finish as : λi -> (λatom -> *).
End_Definition.
```

Operations 
```
Apply in Term : Linear walk in a lambda function in a term and evaluates aplications
Term a : λx -> ((λf -> f) *), change the Term for
Term a : λx -> x

Equal Term and Term : Compare two functions lambda through a identy function lambda
Term one = λx -> x
Term two = λy -> x
Equal one two.

Finish Term as : Y : Seems like equal, but it's applicable in main term and compare any (Term/Lambda).
Finish Term as [X : y] [Y : z] ..., A matching [X, y] that apply X and compare if result is y.

Reducible X : Check if a term can be reduciable, therefore don't have any unknow free variable:
Term y : λx -> (x a)
Reducible y : Error (a isn't know)

ApplyTerms X : Substitue the terms of other terms.
Term y : λy -> x
Term x : λf -> λd -> d
ApplyTerms y = λy -> λf -> λd

Beta-Reduction X in Y in Z : Do a beta-reduction in a term.
Term x : λy -> λx -> (y *)
Beta-Reduction x in y in (λy -> y) =  λx -> ((λy -> y) *)

Type X of Y : Check if a Lambda Type X matching with a type Y
Term x : λy -> x
Type x of (* -> *) : Right

Show : Just Show the lambda functions

Normalization of Term strongly by Y : Uses strongly normalization to reduce a lambda term
Normalization of Any strongly by (* -> (* - > *)) = if any is Type (* -> (* - > *)), so can be applicable to a minimal term.

BetaExpasion Term in X in Y :
Yet not implemented

Recursion of Term in Y : Yet not implemented
```

Why Ane?
Ane is a cool name

If need contanct anything just text me :
camposferreiratiago@gmail.com






