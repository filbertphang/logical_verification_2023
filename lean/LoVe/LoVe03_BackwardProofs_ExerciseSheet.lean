/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
  a → a :=
  by
    intro a
    exact a

theorem K (a b : Prop) :
  a → b → b :=
  by
    intro _a b
    exact b

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  by
    intro f b a
    exact f a b

theorem proj_fst (a : Prop) :
  a → a → a :=
  by
    intro a1 _a2
    exact a1

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  by
    intro _a1 a2
    exact a2

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  by
    intro _f a g _b
    exact g a

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  by
    intro f nb a -- can intro a since ¬a = a → False
    apply nb -- since ¬b = b → False
    apply f
    apply a

    -- solution using rewrites:
    -- (a lot more intuitive for me)
    -- intro f nb
    -- rw [Not] at nb
    -- rw [Not]
    -- intro a
    -- apply nb
    -- apply f
    -- exact a

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    {
      intro lhs
      apply And.intro
      {
        intro x
        apply And.left
        exact lhs x
      }
      {
        intro x
        apply And.right
        exact lhs x
      }
    }
    {
      intro lhs x
      apply And.intro
      -- apply "And.left lhs" to the current goal!
      -- should give us ∀ (x:a), P x
      -- which can be applied to the target: P x
      { apply And.left lhs }
      { apply And.right lhs }
    }


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
  mul 0 n = 0 :=
  by
    induction n with
      | zero => rfl
      | succ n' => {
        -- i can't get rid of my Natural Number Game habits
        -- of abusing rw
        rw [mul]
        rw [n_ih]
        rw [add_zero]
      }

#check add_succ
theorem mul_succ (m n : ℕ) :
  mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
      | zero => rfl
      | succ n' =>
        -- manual way
        -- would be easier if i had a way to rewrite a specific
        -- part of the target
        rw [add_comm]
        rw [mul]
        rw [mul]
        rw [n_ih]
        rw [add_succ]
        rw [add_succ]
        -- using ac_rfl because im lazy to do the
        -- shuffling of the positions of n' and m
        ac_rfl

        -- -- easy way
        -- simp [mul, n_ih, add, add_succ]
        -- ac_rfl
        -- doing it manually seems really painful (given the tools we have)

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  by
    induction n with
      | zero =>
        rw [mul_zero]
        rfl
      | succ n' n_ih =>
        rw [mul]
        rw [n_ih]
        rw [mul_succ]
        rw [add_comm]

-- aside: i can't believe they went through most of
-- the Natural Number Game in like one chapter of the book

-- thats wack
theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
      | zero => rfl
      | succ n' =>
        rw [mul]
        rw [n_ih]
        rw [← mul_add]
        -- again, using ac_rfl because shuffling around the terms
        -- using commutativity is like kinda impossible using only rw
        -- need some more targeted rewrites
        ac_rfl

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

-- ^ holy shit you can do that??
-- that would've been helpful to know for the earlier part

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
   by
    rw [mul_comm]
    rw [mul_add]

/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

-- had to refer to proofwiki for this one,
-- because i didn't know how to prove it backwards
-- https://proofwiki.org/wiki/Peirce%27s_Law_is_Equivalent_to_Law_of_Excluded_Middle


theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
  by
    rw [ExcludedMiddle, Peirce]
    intro em a b f
    apply Or.elim
    -- hypothesis
    -- define what ?a and ?b are when using Or.elim
    -- here, define ?a = a and ?b = ¬a
    case h =>
      apply em

    -- left case: a is true
    -- prove that a implies a
    case left =>
      -- obviously, if a is true, then a is true.
      intro a'
      apply a'

    -- right case: ¬a is true, i.e. a is false
    -- prove that ¬a implies a
    case right =>
      -- suppose we have ¬a. then it suffices to prove a
      intro na
      -- since we have f, then it suffices to prove (a → b)
      apply f
      -- suppose we have some a, then it suffices to prove b
      intro a
      -- the false statement implies any statement,
      -- so we can say that False → b
      apply False.elim
      -- since ¬a = a → False,
      -- it suffices to show that a holds
      apply na
      -- a holds, from our earlier supposition
      apply a


/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
  by
    rw [Peirce, DoubleNegation]
    intro peirce a nna
    apply peirce a False
    intro na
    apply False.elim
    apply nna
    apply na

-- im practicing writing this in prose, because sometimes its a bit
-- unclear how the proof logic works

/-
if we have:
forall a,b, ((a -> b) -> a) -> a

then we need to prove:
forall a, ~~a -> a

suppose that for all a, ~~a. then it suffices to prove: a.

we know that
~~a = ~a -> False = (a -> False) -> False

consider b = False.
then, for some a, we have:
((a -> False) -> a) -> a

if we can prove that ((a -> False) -> a), then we can prove a
hence, it suffices to prove:
(a -> False) -> a

suppose that (a -> False). then it suffices to prove: a.

we know that False -> a (false statement implies every statement).
hence, it suffices to prove False.

since we know that (a -> False) -> False, it suffices to prove that (a -> False).

and we know that (a -> False), by supposition.
hence, our claim is proven.
-/

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem DeMorgans {a b : Prop} :
  ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
  by
    apply Iff.intro
    case mp =>
      intro nor
      apply And.intro
      case left =>
        intro a'
        apply nor
        apply Or.inl
        apply a'
      case right =>
        intro b'
        apply nor
        apply Or.inr
        apply b'
    case mpr =>
      intro and or
      apply Or.elim
      case h =>
        apply or
      case left =>
        apply And.left
        apply and
      case right =>
        apply And.right
        apply and


theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
  by
    rw [DoubleNegation, ExcludedMiddle]
    intro dn a
    apply dn
    intro n_all
    sorry
    -- i'm sorry, i really don't know how to do this?
    -- i even used ProofWiki, which used `cases`
    -- something we haven't been taught yet at this point
    -- i thought i could use De Morgan's to prove something but I
    -- don't think I can? not using solely backwards proofs?
    --
    -- if anyone sees this, please help me :-(
