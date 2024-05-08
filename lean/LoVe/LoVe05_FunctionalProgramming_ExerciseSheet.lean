/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Exercise 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

theorem reverseAccu_Eq_reverse_append {α : Type} :
  ∀as xs : List α, reverseAccu as xs = reverse xs ++ as :=
  fix as xs : List α
  by induction xs generalizing as with
    | nil => simp [reverseAccu, reverse]
    | cons x xs' ih => simp [reverseAccu, reverse, ih]

/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
  reverseAccu [] xs = reverse xs :=
  calc
    reverseAccu [] xs = reverse xs ++ [] :=
      reverseAccu_Eq_reverse_append [] xs
    _ = reverse xs :=
      by simp [append]

/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
  reverseAccu [] (reverseAccu [] xs) = xs :=
  by
    -- one-line achieved :-)
    simp [reverseAccu_Eq_reverse_append, reverseAccu_eq_reverse, reverse_reverse]

/- 1.4. Prove the following theorem by structural induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how
structural induction works (and is good practice for the final exam).

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `rfl` or `simp` need not be
justified if you think they are obvious (to humans), but you should say which
key theorems they depend on. You should be explicit whenever you use a function
definition. -/

-- enter your paper proof here

/- paper proof:

∀as xs : list α, reverseAccu as xs = reverse xs ++ as
we fix this claim for some arbitrary as xs : list α

let P(ys) be the proposition that:
∀as, reverseAccu as ys = reverse ys ++ as

we prove this by induction on ys. we have 2 cases:

case 1: ys is []
for some arbitrary as, we have
reverseAccu as [] = reverse [] ++ as

reverseAccu as []
= as (by reverseAccu.nil)
= [] ++ as (by ← append.nil)
= reverse [] ++ as (by ← reverse.nil)
qed

case 2: ys is y :: ys'
for some arbitrary as, we have
reverseAccu as (y :: ys') = reverse (y :: ys') ++ as

we also have the induction hypothesis:
∀ as : list α , reverseAccu as ys' = reverse ys' ++ as

reverseAccu as (y :: ys')
= reverseAccu (y :: as) ys' (by reverseAccu.cons)
= reverse ys' ++ (y :: as)  (by induction hypothesis)
= reverse ys' ++ (y :: ([] ++ as)) (by ← append.nil)
= reverse ys' ++ ((y :: []) ++ as) (by ← append.cons)
= reverse ys' ++ ([y] ++ as) (by simp on defn of list.cons)
= (reverse ys' ++ [y]) ++ as (by assumed associativity of append?)
= reverse (y :: ys') ++ as (by ← reverse.cons)
qed
-/


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. Define the `take` function, which returns a list consisting of the the
first `n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → List α → List α
  | 0,     _      => []
  | _ + 1, []      => []
  | m + 1, x :: xs => [x] ++ take m xs

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : List α) = [] :=
  fix n : ℕ
  match n with
    | 0 => by simp [drop]
    | _ + 1 => by simp [drop]

@[simp] theorem take_nil {α : Type} :
  ∀n : ℕ, take n ([] : List α) = [] :=
  fix n : ℕ
  match n with
    | 0 => by simp [take]
    | _ + 1 => by simp [take]

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

theorem drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,      _, _         => by rfl
  -- supply the two missing cases here
  | _  + 1, n, []        => by simp [drop]
  | m' + 1, n, x :: xs'  => by
    simp [drop]
    apply drop_drop

theorem take_take {α : Type} :
  ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
  | 0,     _ => by rfl
  | _ + 1, [] => by rfl
  | m + 1, x :: xs => by
    simp [take]
    apply take_take

theorem take_drop {α : Type} :
  ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs
  | 0, _ => by rfl
  | _ + 1, [] => by rfl
  | m + 1, x :: xs => by
    simp [take, drop]
    apply take_drop

-- ^ is it supposed to be so easy? :o

/- ## Question 3: A Type of Terms

3.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

-- enter your definition here
inductive Term : Type where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 3.2 (**optional**). Register a textual representation of the type `term` as
an instance of the `Repr` type class. Make sure to supply enough parentheses to
guarantee that the output is unambiguous. -/

def Term.repr : Term → String
  | var name => name
  | lam name term => "(λ" ++ name ++ ". " ++ Term.repr term ++ ")"
  | app lamb term => "(" ++ Term.repr lamb ++ " " ++ Term.repr term ++ ")"

instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 (**optional**). Test your textual representation. The following command
should print something like `(λx. ((y x) x))`. -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
