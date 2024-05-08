/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume habc : (a → b → c)
  assume hb : b
  assume ha : a
  have hbc : b → c :=
    habc ha
  show c from
    hbc hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from
    ha1

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from
    ha2

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume fabc : (a → b → c)
  assume ha : a
  assume fac : a → c
  assume hb : b
  show c from
    fac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume fab : a → b
  assume hnb : ¬b
  show ¬a from
    assume ha : a
    hnb (fab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro (
    assume hapqx : (∀ (x : α), p x ∧ q x)
    have hapx : (∀ (x : α), p x) :=
      fix ha : α
      And.left (hapqx ha)
    have haqx : (∀ (x : α), q x) :=
      fix ha : α
      And.right (hapqx ha)
    show (∀x, p x) ∧ (∀x, q x) from
      And.intro hapx haqx
  )
  (
    assume hapaqx : (∀ (x : α), p x) ∧ (∀ (x : α), q x)
    fix ha : α
    have hpa : p ha :=
      (And.left hapaqx) ha
    have hqa : q ha :=
      (And.right hapaqx) ha
    show p ha ∧ q ha from
      And.intro hpa hqa
  )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  -- getting lazy to type out these long statements
  -- so i'll just use type inference
  assume hexaypxy : _
  fix hy : α
  sorry

/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
  (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by
      rw [mul_add]
      rw [mul_comm]
      rw [mul_comm (a+b)]
  _ = a * a + a * b + b * a + b * b :=
    by
      rw [mul_add, mul_add]
      simp [add_assoc]
  _ = a * a + a * b + a * b + b * b :=
    by
      rw [mul_comm b]
  _ = a * a + 2 * a * b + b * b :=
    by
      -- wrangling with commutativity and associativity is quite annoying
      rw [add_comm, add_assoc]
      rw [← Nat.two_mul]
      ac_rfl

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have l1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by
      rw [mul_add]
      rw [mul_comm]
      rw [mul_comm (a+b)]
  have l2 : a * (a + b) + b * (a + b)  = a * a + a * b + b * a + b * b :=
    by
      rw [mul_add, mul_add]
      simp [add_assoc]
  have l3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by
      rw [mul_comm b]
  have l4 :  a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by
      rw [add_comm, add_assoc]
      rw [← Nat.two_mul]
      ac_rfl
  show _ from
    -- chain the equality using transitivity
    Eq.trans l1 (
      Eq.trans l2 (
        Eq.trans l3 l4
      )
    )

/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  -- proof by counterexample
  -- introduce P and backwards clause for one_point_wrong
  let P (x: ℕ) := x = 0
  let opw := All.one_point_wrong 0 P
  let opwb := Iff.mpr opw
  -- show that P 0 holds (obviously)
  have p0 : P 0 :=
    by
      simp
  -- show that the forall statement holds
  have fa :=
    opwb p0
  -- show that the instance where x=3 holds, by universality
  have fa3 :=
    fa 3
  -- show that this implies that 3 = 0
  have three_eq_zero : 3 = 0 :=
    And.left fa3
  -- show that 3 = 0 is blatantly false
  have three_eq_zero_wrong : 3 = 0 -> False :=
    by
      simp
  -- qed
  show _ from
    three_eq_zero_wrong three_eq_zero


/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  -- proof by counterexample
  -- set up sample P and forward clause of one_point_wrong
  let P (x: ℕ) := x = 0
  let opw := Exists.one_point_wrong 3 P
  let opwf := Iff.mp opw
  -- show that P 3 holds
  have p3 : P 3 :=
    by
      apply opwf
      apply Exists.intro 2
      simp
  -- show that P 3 is false
  have p3_wrong : P 3 -> False :=
    by
      simp
  -- qed
  show False from
    p3_wrong p3

end LoVe
