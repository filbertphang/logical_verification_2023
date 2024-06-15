/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
--           name      value, possibly depending on another variable
  | assign : String → (State → ℕ) → Stmt
--           assertion, possibly depending on a variable
  | assert : (State → Prop) → Stmt
--           first  second
  | seq    : Stmt → Stmt → Stmt
--           list of choices
  | choice : List Stmt → Stmt
--           statement to loop
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  -- enter the missing `assign` rule here
  | assign (name) (B s) : BigStep (Stmt.assign name B, s) (s[name ↦ B s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- enter the missing `seq` rule here
  | seq (S T s u t) (hS : BigStep (S, s) u) (hT : BigStep (T, u) t): BigStep (Stmt.seq S T, s) t
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- enter the missing `loop` rules here
  | loop_noop (S s) : BigStep (Stmt.loop S, s) s
  | loop_op (S s t u) (h0 : BigStep (S, s) t) (h1 : BigStep (Stmt.loop S, t) u) : BigStep (Stmt.loop S, s) u

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    {
      intro h
      cases h with
      | assign _ _ => rfl
    }
    {
      intro h
      rw [h]
      apply BigStep.assign
    }

@[simp] theorem BigStep_assert {B s t} :
  (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
  by
    apply Iff.intro
    {
      intro h
      cases h with
      | assert =>
        apply And.intro
        { rfl }
        { exact hB }
    }
    {
      intro h
      rw [And.left h]
      apply BigStep.assert
      exact And.right h
    }

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
  (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
  by
    apply Iff.intro
    {
      intro h
      cases h with
      | seq =>
        apply Exists.intro u
        exact And.intro hS hT
    }
    {
      intro h
      match h with
      -- construct a BigStep judgement of the required type
      | ⟨u, lhs, rhs⟩ => exact BigStep.seq S₁ S₂ s u t lhs rhs
    }

theorem BigStep_loop {S s u} :
  (Stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  by
    apply Iff.intro
    {
      intro h
      cases h with
      | loop_noop =>
        apply Or.inl
        rfl
      | loop_op =>
        apply Or.inr
        apply Exists.intro t
        exact And.intro h0 h1
    }
    {
      intro h
      -- show that in either case of the hypothesis,
      -- the BigStep judgement holds
      cases h
      {
        -- case 1: loop no-op
        rw [← h_1]
        apply BigStep.loop_noop
      }
      {
        -- case 2: loop op
        match h_1 with
        -- use match statement to "instantiate" the existential hypothesis
        -- i.e. construct such a state `t` where the above holds
        -- then construct such a judgement to prove that it exists
        | ⟨t, lhs, rhs⟩  =>
          exact BigStep.loop_op S s t u lhs rhs
      }
    }

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
  (Stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
  by
    apply Iff.intro
    {
      intro h
      cases h with
      | choice =>
        apply Exists.intro i
        apply Exists.intro hless
        exact hbody
    }
    {
      intro h
      match h with
      | ⟨i, hless, body⟩ => exact BigStep.choice Ss s t i hless body
    }

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    GCL.Stmt.assign x a
  | S; T =>
    gcl_of S ; gcl_of T
  | Stmt.ifThenElse B S T  =>
    -- this models both possibilities happening
    -- however, since either option may be chosen, the program may
    -- terminate instead of executing the correct branch
    GCL.Stmt.choice [GCL.Stmt.assert B ; gcl_of S, GCL.Stmt.assert (fun s ↦ ¬(B s)); gcl_of T]
  | Stmt.whileDo B S =>
    -- not sure if i should recurse directly back into the assert/S sequence
    -- instead of using a loop statement
    -- i.e. GCL.Stmt.assert B ; gcl_of S ; gcl_of (Stmt.whileDo B S)
    GCL.Stmt.loop (GCL.Stmt.assert B ; gcl_of S)

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- assigning something to itself, e.g. assign "arbitrary" (fun s ↦ s "arbitrary")


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
  S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
  S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
  S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
  Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by
    -- apparently, simp magically does everything
    rw [BigStepEquiv]
    simp

theorem BigStepEquiv.seq_skip_left {S} :
  Stmt.skip; S ~ S :=
  by
    rw [BigStepEquiv]
    simp

theorem BigStepEquiv.seq_skip_right {S} :
  S; Stmt.skip ~ S :=
  by
    rw [BigStepEquiv]
    simp

theorem BigStepEquiv.if_seq_while_skip {B S} :
  Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
  by
    rw [BigStepEquiv]
    intro s t
    apply Iff.intro
    {
      intro h
      -- intentionally not using simp in the body here as an exercise
      cases h with
      | if_true =>
        rw [BigStep_while_true_Iff hcond]
        rw [BigStep_seq_Iff] at hbody
        exact hbody
      | if_false =>
        rw [BigStep_while_false_Iff hcond]
        rw [BigStep_skip_Iff] at hbody
        exact hbody
    }
    {
      intro h
      simp
      -- consider both while/true and while/false cases
      -- prove different parts of the Or statement accordingly
      cases h with
      | while_true =>
        apply Or.inl
        apply And.intro
        { exact hcond }
        {
          apply Exists.intro t_1
          apply And.intro
          { exact hbody }
          { exact hrest }
        }
      | while_false =>
        apply Or.inr
        apply And.intro
        { exact hcond }
        { rfl }
    }

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
    (hT : T₁ ~ T₂) :
  S₁; T₁ ~ S₂; T₂ :=
  by
    rw [BigStepEquiv]
    intro s t
    apply Iff.intro
    {
      intro h
      simp
      cases h with
      | seq =>
        apply Exists.intro t_1
        apply And.intro
        {
          rw [hS] at hS_1
          exact hS_1
        }
        {
          rw [hT] at hT_1
          exact hT_1
        }
    }
    {
      intro h
      simp
      cases h with
      | seq =>
        apply Exists.intro t_1
        apply And.intro
        {
          rw [← hS] at hS_1
          exact hS_1
        }
        {
          rw [← hT] at hT_1
          exact hT_1
        }
    }

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    rw [BigStepEquiv]
    intro s t
    apply Iff.intro
    {
      intro h
      simp at *
      rw [← hS, ← hT]
      exact h
    }
    {
      intro h
      simp at *
      rw [hS, hT]
      exact h
    }

end LoVe
