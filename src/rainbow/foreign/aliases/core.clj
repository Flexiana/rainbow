(ns rainbow.foreign.aliases.core
  "Lean/Mathlib constant aliases of the core ingestion stage (frozen data).")

;; constant-aliases: data recorded from an earlier proving run (pure data, not recomputed here)
(def constant-aliases
'{"Iff.mpr" proposition/equivalence-backward,
 "And" proposition/conjunction,
 "Exists" proposition/existence,
 "Eq.refl" equality/reflexive,
 "And.intro" proposition/conjoin,
 "Function.Injective" function/injective,
 "True.intro" proposition/trivial,
 "Exists.intro" proposition/witness,
 "Or.inl" proposition/left-disjunct,
 "Not" proposition/negation,
 "ExistsUnique" proposition/unique-existence,
 "Or.inr" proposition/right-disjunct,
 "Function.Bijective" function/bijective,
 "False" proposition/falsity,
 "Or.elim" proposition/use-disjunction,
 "Exists.elim" proposition/use-witness,
 "Function.Involutive" function/involutive,
 "Or" proposition/disjunction,
 "ExistsUnique.intro" proposition/unique-witness,
 "Eq" equality/Eq,
 "Function.Surjective" function/surjective,
 "Iff" proposition/equivalence,
 "ExistsUnique.elim" proposition/use-unique-witness,
 "Iff.intro" proposition/equivalence-intro,
 "False.elim" proposition/explode,
 "And.right" proposition/right,
 "True" proposition/truth,
 "Exists.fst" logic/exists-proof-first,
 "And.left" proposition/left,
 "Ne" equality/inequality,
 "Iff.mp" proposition/equivalence-forward}
  )
