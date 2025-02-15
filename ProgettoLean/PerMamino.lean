import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.CauSeq.Completion



inductive ExpRingTerm  where
  | base : ℤ → ExpRingTerm
  | exp : ExpRingTerm → ExpRingTerm
  | add : ExpRingTerm → ExpRingTerm → ExpRingTerm
  | mul : ExpRingTerm → ExpRingTerm → ExpRingTerm

instance : Add ExpRingTerm where
  add := ExpRingTerm.add

instance : Mul ExpRingTerm where
  mul := ExpRingTerm.mul

class Exp (α : Type u) where
  exp : α → α

instance : Exp ExpRingTerm where
  exp := ExpRingTerm.exp


-- def ExpRingTerm.Equiv (x y : ExpRingTerm) : Prop :=
--   match x, y with
--   | ExpRingTerm.base a, ExpRingTerm.base b => a = b
--   | ExpRingTerm.exp a, ExpRingTerm.exp b => ExpRingTerm.Equiv a b
--   | ExpRingTerm.add a b, ExpRingTerm.add c d => (ExpRingTerm.Equiv a c ∧ ExpRingTerm.Equiv b d) ∨ (ExpRingTerm.Equiv a d ∧ ExpRingTerm.Equiv b c)
--   | ExpRingTerm.mul a b, ExpRingTerm.mul c d => ExpRingTerm.Equiv a c ∧ ExpRingTerm.Equiv b d
--   | _, _ => sorry

inductive ExpRingTerm.Rel : ExpRingTerm → ExpRingTerm → Prop
  -- base cases
  | base_eq (a b : ℤ): (a=b)-> ExpRingTerm.Rel (ExpRingTerm.base a) (ExpRingTerm.base b)
  | exp_fun (a b : ExpRingTerm) : ExpRingTerm.Rel a b → ExpRingTerm.Rel (ExpRingTerm.exp a) (ExpRingTerm.exp b)
  | add_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (ExpRingTerm.add a b) (ExpRingTerm.add c d)
  | mul_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (ExpRingTerm.mul a b) (ExpRingTerm.mul c d)

  -- | refl (a : ExpRingTerm) : ExpRingTerm.Rel a a
  -- | symm (a b : ExpRingTerm) : ExpRingTerm.Rel b a
  -- | trans (a b c : ExpRingTerm) : ExpRingTerm.Rel a b → ExpRingTerm.Rel b c → ExpRingTerm.Rel a c

  -- recursive axioms
  | add_comm (a b : ExpRingTerm) : ExpRingTerm.Rel (a + b) (b + a)
  | mul_comm (a b : ExpRingTerm) : ExpRingTerm.Rel (a * b) (b * a)
  | add_assoc (a b c : ExpRingTerm) : ExpRingTerm.Rel (a + (b + c)) ((a + b) + c)
  | mul_assoc (a b c : ExpRingTerm) : ExpRingTerm.Rel (a * (b * c)) ((a * b) * c)
  | add_zero (a : ExpRingTerm) : ExpRingTerm.Rel (a + (ExpRingTerm.base 0)) a
  | mul_one (a : ExpRingTerm) : ExpRingTerm.Rel ( a * (ExpRingTerm.base 1)) a
  | add_inv (a : ExpRingTerm) : ExpRingTerm.Rel (a + (a + (exp a))) (ExpRingTerm.base 0)
  | add_mul (a b c : ExpRingTerm) : ExpRingTerm.Rel ((a + b) * c) ((a * c) + (b * c))
  | mul_add (a b c : ExpRingTerm) : ExpRingTerm.Rel (a * (b + c)) ((a * b) + (a * c))
  | exp_add (a b : ExpRingTerm) : ExpRingTerm.Rel (exp (a + b)) ((exp a) * (exp b))
  | exp_zero : ExpRingTerm.Rel (exp (ExpRingTerm.base 0)) (ExpRingTerm.base 1)

instance : IsEquiv _ ExpRingTerm.Rel where
  refl := by
    intro x
    induction x
    case base a =>
     apply ExpRingTerm.Rel.base_eq a a
     rfl
    case exp x ih =>
      exact ExpRingTerm.Rel.exp_fun x x ih
    case add x y ih_x ih_y =>
      exact ExpRingTerm.Rel.add_fun x y x y ih_x ih_y
    case mul x y ih_x ih_y =>
      exact ExpRingTerm.Rel.mul_fun x y x y ih_x ih_y

  symm := by
    sorry
    -- intro x y h
    -- induction h
    -- case base_eq a b => exact ExpRingTerm.Rel.base_eq b a

  trans := sorry

instance : Setoid ExpRingTerm := ⟨
  ExpRingTerm.Rel,
  refl, symm, Trans.trans
⟩

def FreeExpRing := Quotient (inferInstanceAs (Setoid ExpRingTerm))

-- instance : IsEquiv _ ExpRingTerm.Equiv where
--   refl := by
--     intro x
--     induction x
--     case base => exact rfl
--     case exp x ih =>
--       exact ih
--     case add x y ih_x ih_y =>
--       left
--       exact ⟨ih_x, ih_y⟩
--     case mul x y ih_x ih_y =>
--       exact ⟨ih_x, ih_y⟩
--   symm := by
--     intro x y h
--     induction x
--     induction y
--     case base a b =>
--       have h2 : a = b := ExpRingTerm.Equiv (ExpRingTerm.base a) (ExpRingTerm.base b)



--   trans := by
--     sorry

-- instance : Setoid ExpRingTerm := ⟨
--   ExpRingTerm.Equiv,
--   refl, symm, Trans.trans
-- ⟩

-- def FreeExpRing := Quotient (inferInstanceAs (Setoid ExpRingTerm))




class ExpRing (α : Type u) extends (Add α), (Mul α), (CommRing α) where

  to_term : α → ExpRingTerm
  base : ℤ → α
  exp : α  → α
  base_hom (a b : ℤ)  : base ( a + b )= (base a) + (base b)
  exp_hom (a b : α) : exp ( a + b ) = (exp a )* (exp b)
  exp_zero : (exp (base 0))  = base 1
  to_term_base (a: ℤ) : (to_term (base a))= ExpRingTerm.base a
  to_term_add (a b : α ) : (to_term (a + b))= (ExpRingTerm.add (to_term a) (to_term b))
  to_term_mul (a b : α ) : (to_term (a * b)) =(ExpRingTerm.mul (to_term a) (to_term b))
  to_term_exp (a :α ) : (to_term (exp a )) = (ExpRingTerm.exp) (to_term a)

class ExpCast (α : Type u) [ExpRing α] (K: Type u) where
  expCast : α → K

class Expcast1 (K: Type u) where
  expCast1 : ExpRingTerm → K

noncomputable def expcast1  : (ExpRingTerm →  Real ):=
(fun x => match x with
          |ExpRingTerm.base q => (q: ℝ)
          |ExpRingTerm.add a b => (expcast1 a) + (expcast1 b)
          |ExpRingTerm.mul a b => (expcast1 a) * (expcast1 b)
          |ExpRingTerm.exp a => Real.exp (expcast1 a))


noncomputable instance expcast α [ExpRing α ] : ExpCast α Real where
  expCast x := expcast1 (ExpRing.to_term x)
