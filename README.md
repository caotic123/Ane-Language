# Ane-Language

Ane is a tool-language to analyze lambda terms that's ensure a real time manipulation of lambda terms.
Ane uses total untyped lambda calculus, therefore terms can be easily changed and makes assumptions.

Example ::

```
Definition : pair.
Term pair : λx -> λy -> λf -> λi -> ((f x) y).
End_Terms.

Beta-Reduction pair in x in λp -> *.
Beta-Reduction pair in y in λp -> (* *).
Apply pair.
Finish as [λx -> λy -> x : (λi -> λp -> *)]
          [λx -> λy -> y : (λi -> λp -> (* *))].
End_Definition.

Definition : NaturalNumbers.

Term zero : λx -> x.
Term S : λf -> λn -> (f n).
Term One : (λi -> ((S zero) i)).
Term Second : (λi -> ((S (S zero)) i)).
Term Three : (λi -> ((S (S (S zero))) i)).
End_Terms.

Apply-Terms One.
Apply One.
Apply One.
End_Definition.
```
