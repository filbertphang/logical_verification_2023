/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
  Odd 1 :=
  by
    intro h
    cases h

/- 1.2. Prove that 3 and 5 are odd. -/

theorem Odd_3 :
  Odd 3 :=
  by
    intro h
    cases h
    apply Odd_1
    exact a

theorem Odd_5 :
  Odd 5 :=
  by
    intro h
    cases h
    apply Odd_3
    exact a

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
  ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 =>
    by
      simp [mul_add]
      apply Even.add_two
      exact Even_two_times m

/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  -- enter the missing cases here
  where
    | vs : ∀ m n : ℕ, m > n → ServAhead (m – n)
    | advServ : ServAhead (Score.advServ)
    | gameServ : ServAhead (Score.gameServ)


/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
  ServAhead (Score.vs m n) :=
  ServAhead.vs m n hgt

theorem ServAhead_advServ :
  ServAhead Score.advServ :=
  ServAhead.advServ

theorem not_ServAhead_advRecv :
  ¬ ServAhead Score.advRecv :=
  by
    intro h
    cases h

theorem ServAhead_gameServ :
  ServAhead Score.gameServ :=
  ServAhead.gameServ

theorem not_ServAhead_gameRecv :
  ¬ ServAhead Score.gameRecv :=
  by
    intro h
    cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

/-
We only need to implement rules(?) on our inductive hypothesis
corresponding to the constructors of Score that we want
it to hold for.

e.g., we want ServAhead to hold when we have Score.advServ,
so we implement a constructor for that.
But we don't bother implementing a constructor for Score.advRecv,
since we don't want ServAhead to be True in that scenario.
-/



/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
  ∀t : BTree α, IsFull (mirror t) → IsFull t :=
  sorry

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def BTree.map {α β : Type} (f : α → β) : BTree α → BTree β :=
  sorry

/- 3.3. Prove the following theorem by case distinction. -/

theorem BTree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : BTree α, BTree.map f t = BTree.empty ↔ t = BTree.empty :=
  sorry

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem BTree.map_mirror {α β : Type} (f : α → β) :
  ∀t : BTree α, IsFull t → IsFull (BTree.map f t) :=
  sorry

end LoVe
