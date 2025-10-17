# FF - Finite Field system resolution via CVC5 and proof reconstruction

## The 'What'.

Resolves systems of `ZMod p` equations.

```
example {a b c d e f : ZMod 41} [Fact (Nat.Prime 41)]
  (P4: a*b -a -b +c = 0)
  (P5: b*c +d -b -c = 0)
  (P6: a*b -a -b +e = 0)
  (P7: b*e +f -b -e = 0) :
  f - d = 0 := by
  FF
```

## Installation.

Put the following in your `lakefile.lean`:
```
require ff from git
  "https://github.com/NethermindEth/LeanFF/" @ "main"
```

You can now `import FF` and call the `FF` tactic.

## The 'How' and 'Why'.
`FF` uses Gröbner basis solver implemented in cvc5 together with proof reconstruction on Lean side to combine the efficiency of SMT solvers with trustworthiness of Lean.

## The 'Yikes'.
As it stands right now, `grind` is faster than `FF` :(. TODO - Are we going to find some big example?
