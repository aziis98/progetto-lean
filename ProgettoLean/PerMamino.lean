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

instance : Neg ExpRingTerm where
  neg x := ExpRingTerm.mul (ExpRingTerm.base (-1)) x

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
  -- | base_eq (a b : ℤ) : (a = b) → ExpRingTerm.Rel (ExpRingTerm.base a) (ExpRingTerm.base b)
  | add_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (ExpRingTerm.add a b) (ExpRingTerm.add c d)
  | mul_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (ExpRingTerm.mul a b) (ExpRingTerm.mul c d)
  | exp_fun (a b : ExpRingTerm) : ExpRingTerm.Rel a b → ExpRingTerm.Rel (ExpRingTerm.exp a) (ExpRingTerm.exp b)

  | refl (a : ExpRingTerm) : ExpRingTerm.Rel a a
  | symm (a b : ExpRingTerm) : ExpRingTerm.Rel a b → ExpRingTerm.Rel b a
  | trans (a b c : ExpRingTerm) : ExpRingTerm.Rel a b → ExpRingTerm.Rel b c → ExpRingTerm.Rel a c

  -- recursive axioms
  | add_comm (a b : ExpRingTerm) : ExpRingTerm.Rel (a + b) (b + a)
  | mul_comm (a b : ExpRingTerm) : ExpRingTerm.Rel (a * b) (b * a)
  | add_assoc (a b c : ExpRingTerm) : ExpRingTerm.Rel ((a + b) + c) (a + (b + c))
  | mul_assoc (a b c : ExpRingTerm) : ExpRingTerm.Rel ((a * b) * c) (a * (b * c))

  | zero_add (a : ExpRingTerm) : ExpRingTerm.Rel ((ExpRingTerm.base 0) + a) a
  | add_zero (a : ExpRingTerm) : ExpRingTerm.Rel (a + (ExpRingTerm.base 0)) a

  | add_inv (a : ExpRingTerm) : ExpRingTerm.Rel ((-a) + a) (ExpRingTerm.base 0)

  | mul_one (a : ExpRingTerm) : ExpRingTerm.Rel ( a * (ExpRingTerm.base 1)) a
  | add_mul (a b c : ExpRingTerm) : ExpRingTerm.Rel ((a + b) * c) ((a * c) + (b * c))
  | mul_add (a b c : ExpRingTerm) : ExpRingTerm.Rel (a * (b + c)) ((a * b) + (a * c))
  | exp_add (a b : ExpRingTerm) : ExpRingTerm.Rel (exp (a + b)) ((exp a) * (exp b))
  | exp_zero : ExpRingTerm.Rel (exp (ExpRingTerm.base 0)) (ExpRingTerm.base 1)

instance : IsEquiv _ ExpRingTerm.Rel where
  refl := by
    -- intro x
    -- induction x
    -- case base a =>
    --  apply ExpRingTerm.Rel.base_eq a a
    --  rfl
    -- case exp x ih =>
    --   exact ExpRingTerm.Rel.exp_fun x x ih
    -- case add x y ih_x ih_y =>
    --   exact ExpRingTerm.Rel.add_fun x y x y ih_x ih_y
    -- case mul x y ih_x ih_y =>
    --   exact ExpRingTerm.Rel.mul_fun x y x y ih_x ih_y
    exact ExpRingTerm.Rel.refl

  symm := by
    -- intro _ _ h
    -- induction h
    -- case base_eq a b h =>
    --   exact ExpRingTerm.Rel.base_eq b a h.symm
    -- case exp_fun a b h1 h2 =>
    --   exact ExpRingTerm.Rel.exp_fun b a h2
    -- case add_fun a b c d h1 h2 h3 h4 =>
    --   exact ExpRingTerm.Rel.add_fun c d a b h3 h4
    -- case mul_fun a b c d h1 h2 h3 h4 =>
    --   exact ExpRingTerm.Rel.mul_fun c d a b h3 h4
    -- case add_comm a b =>
    --   exact ExpRingTerm.Rel.add_comm b a
    -- case mul_comm a b =>
    --   exact ExpRingTerm.Rel.mul_comm b a
    -- case add_assoc a b c a' b' =>
    --   sorry
    exact ExpRingTerm.Rel.symm

  trans := by
    exact ExpRingTerm.Rel.trans




instance instSetoid : Setoid ExpRingTerm := ⟨
  ExpRingTerm.Rel,
  refl, symm, Trans.trans
⟩

def FreeExpRing := Quotient (inferInstanceAs (Setoid ExpRingTerm))

def FreeExpRing.of (x : ExpRingTerm) : FreeExpRing :=
  Quotient.mk instSetoid x

instance : Zero FreeExpRing where
  zero := FreeExpRing.of (ExpRingTerm.base 0)

instance : One FreeExpRing where
  one := FreeExpRing.of (ExpRingTerm.base 1)

instance : Add FreeExpRing where
  add := Quotient.lift₂ (fun x y => FreeExpRing.of (ExpRingTerm.add x y)) (by
    intro a b c d h1 h2
    dsimp
    apply Quotient.sound
    exact ExpRingTerm.Rel.add_fun a b c d h1 h2
  )

instance : Mul FreeExpRing where
  mul := Quotient.lift₂ (fun x y => FreeExpRing.of (ExpRingTerm.mul x y)) (by
    intro a b c d h1 h2
    dsimp
    apply Quotient.sound
    exact ExpRingTerm.Rel.mul_fun a b c d h1 h2
  )

instance : Exp FreeExpRing where
  exp := Quotient.lift (fun x => FreeExpRing.of (ExpRingTerm.exp x)) (by
    intro a b h
    dsimp
    apply Quotient.sound
    exact ExpRingTerm.Rel.exp_fun a b h
  )

open ExpRingTerm

#check FreeExpRing.of (base 1) + (Exp.exp (FreeExpRing.of (ExpRingTerm.base 1)))

lemma my_add_assoc (a b c : FreeExpRing) : (a + b) + c = a + (b + c) := by
    let a' := a.exists_rep
    let b' := b.exists_rep
    let c' := c.exists_rep

    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    rcases c' with ⟨c', hc⟩

    have assoc : ExpRingTerm.Rel (a' + b' + c') (a' + (b' + c')) := ExpRingTerm.Rel.add_assoc a' b' c'

    have h1 : ⟦a' + b' + c'⟧ = a + b + c := by
      rw [← ha, ← hb, ← hc]
      rfl

    have h2 : ⟦a' + (b' + c')⟧ = a + (b + c) := by
      rw [← ha, ← hb, ← hc]
      rfl

    rw [← h1, ← h2]

    exact Quotient.sound assoc

lemma my_add_zero (a : ExpRingTerm) : FreeExpRing.of a + FreeExpRing.of (ExpRingTerm.base 0) = FreeExpRing.of a :=
  by
    have h1 : FreeExpRing.of (a + ExpRingTerm.base 0) = FreeExpRing.of a := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_zero

    rw [← h1]

    apply Quotient.sound
    apply ExpRingTerm.Rel.add_zero

lemma my_add_comm: ∀ (a b : FreeExpRing), a + b = b + a := by
    intro a b
    let a' := a.exists_rep
    let b' := b.exists_rep

    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩

    have comm : ExpRingTerm.Rel (a' + b') (b' + a') := ExpRingTerm.Rel.add_comm a' b'

    have h1 : ⟦a' + b'⟧ = a + b := by
      rw [← ha, ← hb]
      rfl

    have h2 : ⟦b' + a'⟧ = b + a := by
      rw [← ha, ← hb]
      rfl

    rw [← h1, ← h2]

    exact Quotient.sound comm

lemma add_cancel (a b c : ExpRingTerm) : FreeExpRing.of a + FreeExpRing.of b = FreeExpRing.of a + FreeExpRing.of c → FreeExpRing.of b = FreeExpRing.of c :=
  by
    intro h

    rw [← my_add_zero b, ← my_add_zero c]

    have h1 : FreeExpRing.of ((-a) + a) = FreeExpRing.of (base 0) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_inv

    rw [← h1]

    have h2 : FreeExpRing.of (-a ) + (FreeExpRing.of a) + FreeExpRing.of b = FreeExpRing.of b + FreeExpRing.of (-a + a) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_comm

    have h3 : FreeExpRing.of (-a) + (FreeExpRing.of a) + FreeExpRing.of b = FreeExpRing.of (-a + a) + FreeExpRing.of b := by
      rw [h2]
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_comm

    have h4 : FreeExpRing.of (-a + a) + FreeExpRing.of b = FreeExpRing.of b + FreeExpRing.of (-a + a):= by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_comm
    rw [ ← h4,← h3, my_add_assoc, h, ← my_add_assoc]
    have h5 : FreeExpRing.of (-a + a) = FreeExpRing.of (-a)+ FreeExpRing.of (a)  := by
      apply Quotient.sound
      rfl
    rw [h5]
    rw [my_add_comm]

    -- have h3


lemma my_mul_add (a b c : ExpRingTerm) : FreeExpRing.of (a * (b + c)) = FreeExpRing.of (a * b) + FreeExpRing.of (a * c) := by
  apply Quotient.sound
  apply ExpRingTerm.Rel.mul_add



lemma my_add_mul (a b c : ExpRingTerm) : (FreeExpRing.of (a) + FreeExpRing.of (b)) * FreeExpRing.of (c) = FreeExpRing.of (a * c) + FreeExpRing.of (b * c) := by
  apply Quotient.sound
  apply ExpRingTerm.Rel.add_mul

lemma zero_mul (a : ExpRingTerm) : FreeExpRing.of (ExpRingTerm.base 0 * a) = FreeExpRing.of (ExpRingTerm.base 0) :=
  by
    have h : FreeExpRing.of (ExpRingTerm.add (ExpRingTerm.base 0) (ExpRingTerm.base 0)) = FreeExpRing.of (ExpRingTerm.base (0)) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_zero

    have h1 : FreeExpRing.of (base 0) * (FreeExpRing.of a) = FreeExpRing.of (base 0) * (FreeExpRing.of a) + FreeExpRing.of (base 0) * (FreeExpRing.of a) + (FreeExpRing.of (base 0)):= by

      sorry
      -- nth_rw 1 [← h]
      -- rw[my_add_zero]
      -- apply Quotient.sound
      -- apply ExpRingTerm.Rel.add


    -- apply ExpRingTerm.Rel.












instance : AddCommMonoid FreeExpRing where
  add_assoc := my_add_assoc

  add_comm := my_add_comm

  zero_add := by
    intro a
    let a' := a.exists_rep

    rcases a' with ⟨a', ha⟩

    have h1 : ⟦ExpRingTerm.base 0 + a'⟧ = 0 + a := by
      rw [← ha]
      rfl

    rw [← h1, ← ha]

    exact Quotient.sound (ExpRingTerm.Rel.zero_add a')

  add_zero := by
    intro a
    let a' := a.exists_rep

    rcases a' with ⟨a', ha⟩

    have h1 : ⟦a' + ExpRingTerm.base 0⟧ = a + 0 := by
      rw [← ha]
      rfl

    rw [← h1, ← ha]

    exact Quotient.sound (ExpRingTerm.Rel.add_zero a')

  nsmul := fun n x => (FreeExpRing.of (ExpRingTerm.base n)) * x

  nsmul_zero := by
    intro x
    dsimp
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    have h1 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 * x := by
      rw [← hx]
      rfl

    -- have h2 : ExpRingTerm.base 0 * x' = ExpRingTerm.base 0 := by




    -- have h2 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 := by
    sorry






-- have assoc : ExpRingTerm.Rel (a' + b' + c') (a' + (b' + c')) := ExpRingTerm.Rel.add_assoc a' b' c'

-- exact Quotient.sound assoc







-- instance fewifwep : Add FreeExpRing where
--   add := sorry

-- instance : Ring FreeExpRing where
--   add := Quotient.lift₂ fewifwep.add (by
--     sorry
--   )

--   add_assoc := by
--     sorry




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
