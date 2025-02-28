import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Algebraic.Defs


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
  neg x :=  (ExpRingTerm.base (-1)) * x

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
  | add_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (a + b) (c + d)
  | mul_fun (a b c d : ExpRingTerm) : ExpRingTerm.Rel a c → ExpRingTerm.Rel b d → ExpRingTerm.Rel (a * b) (c * d)
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

  | mul_one (a : ExpRingTerm) : ExpRingTerm.Rel (a * (ExpRingTerm.base 1)) a
  | one_mul (a : ExpRingTerm) : ExpRingTerm.Rel ((ExpRingTerm.base 1) * a) a

  | add_mul (a b c : ExpRingTerm) : ExpRingTerm.Rel ((a + b) * c) ((a * c) + (b * c))
  | mul_add (a b c : ExpRingTerm) : ExpRingTerm.Rel (a * (b + c)) ((a * b) + (a * c))
  | exp_add (a b : ExpRingTerm) : ExpRingTerm.Rel (exp (a + b)) ((exp a) * (exp b))
  | exp_zero : ExpRingTerm.Rel (exp (ExpRingTerm.base 0)) (ExpRingTerm.base 1)

  | add_hom (a b : ℤ) : ExpRingTerm.Rel (ExpRingTerm.base (a + b)) ((ExpRingTerm.base a) + (ExpRingTerm.base b))
  | mul_hom (a b : ℤ) : ExpRingTerm.Rel (ExpRingTerm.base (a * b)) ((ExpRingTerm.base a) * (ExpRingTerm.base b))

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
@[simp]
def FreeExpRing := Quotient (inferInstanceAs (Setoid ExpRingTerm))
@[simp]
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

open ExpRingTerm

lemma neg_fun (a b :ExpRingTerm): a.Rel b → (-a).Rel (-b) := by
  intro h
  have h1: (-a).Rel ((ExpRingTerm.base (-1)) * a) := by
    apply ExpRingTerm.Rel.refl
  have h2: ((ExpRingTerm.base (-1)) * a).Rel ((ExpRingTerm.base (-1)) * b) := by
    apply ExpRingTerm.Rel.mul_fun
    apply ExpRingTerm.Rel.refl
    exact h
  have h3: ((ExpRingTerm.base (-1)) * b).Rel (-b) := by
    apply ExpRingTerm.Rel.refl
  apply ExpRingTerm.Rel.trans (-a) ((base (-1))*a) _
  exact h1
  apply ExpRingTerm.Rel.trans  ((base (-1))*a) ((base (-1))*b) _
  exact h2
  exact h3

instance : Neg FreeExpRing where
  neg := Quotient.lift (fun x => FreeExpRing.of (- x)) (by
    intro a b h
    dsimp
    apply Quotient.sound
    apply neg_fun
    exact h
  )

instance : Exp FreeExpRing where
  exp := Quotient.lift (fun x => FreeExpRing.of (ExpRingTerm.exp x)) (by
    intro a b h
    dsimp
    apply Quotient.sound
    exact ExpRingTerm.Rel.exp_fun a b h
  )

@[simp]
lemma neg_scalar (a :ℤ ) :(- ExpRingTerm.base a).Rel (ExpRingTerm.base (- a)) := by

  have h: (- ExpRingTerm.base a).Rel ((ExpRingTerm.base (-1)) * (ExpRingTerm.base a)):=by
    apply ExpRingTerm.Rel.refl
  apply ExpRingTerm.Rel.trans _  ((ExpRingTerm.base (-1)) * (ExpRingTerm.base a)) _
  exact h
  have h1: (ExpRingTerm.base (-a)).Rel (ExpRingTerm.base ((-1) * a)) := by
    rw[neg_one_mul]
    apply ExpRingTerm.Rel.refl
  apply ExpRingTerm.Rel.trans _  (base (-1 * a)) _
  apply ExpRingTerm.Rel.symm
  apply ExpRingTerm.Rel.mul_hom
  apply ExpRingTerm.Rel.symm
  exact h1



#check FreeExpRing.of (base 1) + (Exp.exp (FreeExpRing.of (ExpRingTerm.base 1)))



lemma fuffa (a: ExpRingTerm) : ⟦a⟧ = FreeExpRing.of a := by
  rfl


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

lemma my_add_zero (a : FreeExpRing) : a + FreeExpRing.of (ExpRingTerm.base 0) = a :=
  by
    have h1 : a + FreeExpRing.of (ExpRingTerm.base 0) = a := by
      let a' := a.exists_rep
      rcases a' with ⟨a', ha⟩
      rw [← ha]
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_zero
    rw [← h1]
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw [← ha]
    apply Quotient.sound
    apply ExpRingTerm.Rel.add_zero

lemma my_add_comm (a b : FreeExpRing) : a + b = b + a := by
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
lemma my_mul_comm (a b :FreeExpRing) : a * b = b * a :=by
  let a' := a.exists_rep
  let b' := b.exists_rep

  rcases a' with ⟨a', ha⟩
  rcases b' with ⟨b', hb⟩

  have comm : ExpRingTerm.Rel (a' * b') (b' * a') := ExpRingTerm.Rel.mul_comm a' b'

  have h1 : ⟦a' * b'⟧ = a * b := by
    rw [← ha, ← hb]
    rfl

  have h2 : ⟦b' * a'⟧ = b * a := by
    rw [← ha, ← hb]
    rfl

  rw [← h1, ← h2]

  exact Quotient.sound comm

lemma add_cancel (a b c : ExpRingTerm) : FreeExpRing.of a + FreeExpRing.of b = FreeExpRing.of a + FreeExpRing.of c → FreeExpRing.of b = FreeExpRing.of c :=
  by
    intro h

    rw [← my_add_zero (FreeExpRing.of b), ← my_add_zero (FreeExpRing.of c)]

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

lemma right_mul (a b c : ExpRingTerm) : a.Rel b→ (a*c).Rel (b*c) := by
  intro h
  apply Rel.mul_fun
  exact h
  apply Rel.refl
lemma left_mul (a b c : ExpRingTerm) : a.Rel b→ (c*a).Rel (c*b) := by
  intro h
  apply Rel.mul_fun
  apply Rel.refl
  exact h

lemma my_mul_add (a b c : ExpRingTerm) : FreeExpRing.of (a * (b + c)) = FreeExpRing.of (a * b) + FreeExpRing.of (a * c) := by
  apply Quotient.sound
  apply ExpRingTerm.Rel.mul_add

lemma my_mul_neg (a b : ExpRingTerm ):  ExpRingTerm.Rel (-(a' * b')) (-a' * b') := by
  have h (m: ExpRingTerm): (base (-1))*m= -m := by
    rfl
  rw[← h,← h]
  apply ExpRingTerm.Rel.symm
  apply ExpRingTerm.Rel.mul_assoc




lemma my_mul_add1 (a b c :FreeExpRing) : a * (b + c) = a * b + a * c := by
  let a' := a.exists_rep
  let b' := b.exists_rep
  let c' := c.exists_rep

  rcases a' with ⟨a', ha⟩
  rcases b' with ⟨b', hb⟩
  rcases c' with ⟨c', hc⟩

  have h1 : ⟦a' * (b' + c')⟧ = a * (b + c) := by
    rw [← ha, ← hb, ← hc]
    rfl

  have h2 : ⟦a' * b' + a' * c'⟧ = a * b + a * c := by
    rw [← ha, ← hb, ← hc]
    rfl

  rw [← h1, ← h2]

  apply my_mul_add

lemma my_add_mul (a b c : ExpRingTerm) : (FreeExpRing.of (a) + FreeExpRing.of (b)) * FreeExpRing.of (c) = FreeExpRing.of (a * c) + FreeExpRing.of (b * c) := by
  apply Quotient.sound
  apply ExpRingTerm.Rel.add_mul

lemma my_add_mul1 (a b c : FreeExpRing) : (a + b) * c = a * c + b * c := by
  let a' := a.exists_rep
  let b' := b.exists_rep
  let c' := c.exists_rep

  rcases a' with ⟨a', ha⟩
  rcases b' with ⟨b', hb⟩
  rcases c' with ⟨c', hc⟩

  have h1 : ⟦(a' + b') * c'⟧ = (a + b) * c := by
    rw [← ha, ← hb, ← hc]
    rfl

  have h2 : ⟦a' * c' + b' * c'⟧ = a * c + b * c := by
    rw [← ha, ← hb, ← hc]
    rfl

  rw [← h1, ← h2]

  apply my_add_mul

lemma my_zero_mul (a : ExpRingTerm) : FreeExpRing.of (ExpRingTerm.base 0 * a) = FreeExpRing.of (ExpRingTerm.base 0) :=
  by
    have h : FreeExpRing.of (ExpRingTerm.add (ExpRingTerm.base 0) (ExpRingTerm.base 0)) = FreeExpRing.of (ExpRingTerm.base (0)) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_zero

    have h1 : FreeExpRing.of (base 0) * (FreeExpRing.of a) = FreeExpRing.of (base 0) * (FreeExpRing.of a) + FreeExpRing.of (base 0) * (FreeExpRing.of a) := by

      nth_rw 1 [← my_add_zero (FreeExpRing.of (base 0))]
      rw[my_add_mul]
      rfl
    nth_rw 1[← my_add_zero (FreeExpRing.of (base 0) * (FreeExpRing.of a))] at h1

    apply add_cancel at h1
    exact h1.symm

lemma my_zero_mul1 (a : FreeExpRing) : 0 * a = 0 := by
  let a' := a.exists_rep
  rcases a' with ⟨a', ha⟩

  have h1 : ⟦ExpRingTerm.base 0 * a'⟧ = 0 * a := by
    rw [← ha]
    rfl

  rw [← ha]
  apply my_zero_mul





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

    rw [← hx]

    apply my_zero_mul

  nsmul_succ := by
    intro n x

    simp

    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    rw [← hx]

    have h  : FreeExpRing.of (ExpRingTerm.base (n + 1 )) = FreeExpRing.of (ExpRingTerm.base n) + FreeExpRing.of (ExpRingTerm.base 1) := by
      apply Quotient.sound

      apply ExpRingTerm.Rel.add_hom
    rw[fuffa]

    rw [h]

    have h1 : FreeExpRing.of x' = ⟦x'⟧ := by
      rfl

    rw [← h1]

    rw [my_add_mul]
    have h2: FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of (x')= FreeExpRing.of (ExpRingTerm.base n * x') := by
      rfl
    rw[fuffa]
    rw [h2]

    have h3 : FreeExpRing.of (ExpRingTerm.base 1 * x') = FreeExpRing.of x' := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.one_mul

    rw [h3]


lemma Quotient_mul (a b: FreeExpRing) : Quotient.out (a*b) ≈ (Quotient.out a)*(Quotient.out b)  := by
  apply Quotient.exact
  have h1: ⟦ Quotient.out (a*b)⟧ = a*b := by
    apply Quotient.out_eq
  have h2: (FreeExpRing.of (Quotient.out a)) * (FreeExpRing.of (Quotient.out b)) = a * b := by
    have h3 : (FreeExpRing.of (Quotient.out a))=a := by
      apply Quotient.out_eq
    have h4 : (FreeExpRing.of (Quotient.out b))=b := by
      apply Quotient.out_eq
    rw[h3]
    rw[h4]
  rw[h1]
  have h3: FreeExpRing.of (Quotient.out a) * FreeExpRing.of (Quotient.out b) =⟦Quotient.out a * Quotient.out b⟧  := by
    rfl
  rw[← h3 ]
  rw[h2]

lemma my_one_mul (a : FreeExpRing) : (FreeExpRing.of (base 1)) * a = a := by
  let a' := a.exists_rep
  rcases a' with ⟨a', ha⟩
  rw[← ha]
  have h1: FreeExpRing.of (ExpRingTerm.base 1 * a') = FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of a' := by
    rfl
  repeat rw[fuffa]
  rw[← h1]
  have h2: FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of a' = FreeExpRing.of a' := by
    apply Quotient.sound
    apply ExpRingTerm.Rel.one_mul
  rw[← h2]
  exact h1


instance : Ring FreeExpRing where
  zsmul_zero':= by
    intro x
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    have h1 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 * x := by
      rw [← hx]
      rfl
    rw [← hx]
    apply my_zero_mul
  left_distrib := by
    intro a b c
    rw[my_mul_add1]
  right_distrib := by
    intro a b c
    rw[my_add_mul1]
  zero_mul := by
    intro a
    rw[my_zero_mul1]
  mul_zero := by
    intro a
    rw[my_mul_comm,my_zero_mul1]
  mul_assoc := by
    intro a b c
    let a' := a.exists_rep
    let b' := b.exists_rep
    let c' := c.exists_rep
    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    rcases c' with ⟨c', hc⟩
    have h1 : ⟦a' * b' * c'⟧ = a * b * c := by
      rw [← ha, ← hb, ← hc]
      rfl
    have h2 : ⟦a' * (b' * c')⟧ = a * (b * c) := by
      rw [← ha, ← hb, ← hc]
      rfl
    rw [← h1, ← h2]
    apply Quotient.sound
    apply ExpRingTerm.Rel.mul_assoc
  one_mul := by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    have h1 : ⟦ExpRingTerm.base 1 * a'⟧ = 1 * a := by
      rw [← ha]
      rfl
    rw [← ha]
    apply Quotient.sound
    apply ExpRingTerm.Rel.one_mul
  mul_one := by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    have h1 : ⟦ExpRingTerm.base 1 * a'⟧ = 1 * a := by
      rw [← ha]
      rfl
    rw [← ha]
    apply Quotient.sound
    apply ExpRingTerm.Rel.mul_one
  zsmul := fun n x => (FreeExpRing.of (ExpRingTerm.base n)) * x
  neg x:= -x
  neg_add_cancel:= by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    apply Quotient.sound
    have h1: (-a' + a') ≈ base 0 := by
      apply ExpRingTerm.Rel.add_inv
    apply ExpRingTerm.Rel.trans _ (-a' + a') _
    apply ExpRingTerm.Rel.refl
    exact h1
  zsmul_succ':=by
    intro n a
    dsimp
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    have h1: FreeExpRing.of (ExpRingTerm.base (n + 1)) = FreeExpRing.of (ExpRingTerm.base n) + FreeExpRing.of (ExpRingTerm.base 1) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_hom
    zify
    simp only [fuffa]
    rw[h1]
    have h2: (FreeExpRing.of (ExpRingTerm.base n ) + FreeExpRing.of (ExpRingTerm.base 1)) * (FreeExpRing.of a') = FreeExpRing.of (base ↑n) * (FreeExpRing.of a')+ FreeExpRing.of (base 1) * (FreeExpRing.of a') := by
      repeat rw[← fuffa]
      rw[my_add_mul1]
    rw[h2]
    rw[my_one_mul]

  zsmul_neg':=by
    intro n a
    dsimp
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    rw[fuffa]
    have h: (base (Int.negSucc n))=  (base (-(n+1))) := by
      rfl
    have h1: FreeExpRing.of (base (-(n+1))) =FreeExpRing.of (- (base (n+1))) :=by
      apply Quotient.sound
      apply ExpRingTerm.Rel.symm
      apply neg_scalar
    rw[h]
    rw[h1]
    apply Quotient.sound
    apply ExpRingTerm.Rel.symm
    apply my_mul_neg
    exact a'
    exact a'



class ERing (α : Type u) extends (Add α), (Mul α), (CommRing α) where

  base : ℤ → α
  exp : α  → α
  base_hom (a b : ℤ)  : base ( a + b )= (base a) + (base b)
  exp_hom (a b : α) : exp ( a + b ) = (exp a )* (exp b)
  exp_zero : (exp (base 0))  = base 1


instance : ERing FreeExpRing where
  base := FreeExpRing.of ∘ ExpRingTerm.base
  exp :=  Exp.exp
  add_assoc := add_assoc
  add_comm := my_add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul:= fun n x => (FreeExpRing.of (ExpRingTerm.base n)) * x
  nsmul_zero := by
    intro x
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    have h1 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 * x := by
      rw [← hx]
      rfl
    rw [← hx]
    apply my_zero_mul
  left_distrib := by
    intro a b c
    rw[my_mul_add1]
  right_distrib := by
    intro a b c
    rw[my_add_mul1]
  zero_mul := by
    intro a
    rw[my_zero_mul1]
  mul_zero := by
    intro a
    rw[my_mul_comm,my_zero_mul1]
  one_mul := by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    have h1 : ⟦ExpRingTerm.base 1 * a'⟧ = 1 * a := by
      rw [← ha]
      rfl
    rw [← ha]
    apply Quotient.sound
    apply ExpRingTerm.Rel.one_mul
  mul_one := by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    have h1 : ⟦ExpRingTerm.base 1 * a'⟧ = 1 * a := by
      rw [← ha]
      rfl
    rw [← ha]
    apply Quotient.sound
    apply ExpRingTerm.Rel.mul_one
  mul_comm := my_mul_comm
  mul_assoc := by
    intro a b c
    let a' := a.exists_rep
    let b' := b.exists_rep
    let c' := c.exists_rep
    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    rcases c' with ⟨c', hc⟩
    have h1 : ⟦a' * b' * c'⟧ = a * b * c := by
      rw [← ha, ← hb, ← hc]
      rfl
    have h2 : ⟦a' * (b' * c')⟧ = a * (b * c) := by
      rw [← ha, ← hb, ← hc]
      rfl
    rw [← h1, ← h2]
    apply Quotient.sound
    apply ExpRingTerm.Rel.mul_assoc
  zsmul := fun n x => (FreeExpRing.of (ExpRingTerm.base n)) * x
  base_hom:= by
    intro a b
    have h1: FreeExpRing.of (ExpRingTerm.base (a + b)) = FreeExpRing.of (ExpRingTerm.base a) + FreeExpRing.of (ExpRingTerm.base b) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_hom
    exact h1
  exp_hom:= by
    intro a b
    let a' := a.exists_rep
    let b' := b.exists_rep
    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    rw[← ha]
    rw[← hb]
    have h1: FreeExpRing.of (ExpRingTerm.exp (a' + b')) = FreeExpRing.of (ExpRingTerm.exp a' * ExpRingTerm.exp b') := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.exp_add
    exact h1
  exp_zero:= by
    have h1: FreeExpRing.of (ExpRingTerm.exp (ExpRingTerm.base 0)) = FreeExpRing.of (ExpRingTerm.base 1) := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.exp_zero
    exact h1
  neg_add_cancel:=by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    rw[fuffa]
    have h: -(FreeExpRing.of a') = FreeExpRing.of (- a') := by
      rfl
    rw[h]
    have h1: FreeExpRing.of (-a') + FreeExpRing.of a' = FreeExpRing.of (-a' + a') := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.refl
    rw[h1]
    apply Quotient.sound
    apply ExpRingTerm.Rel.add_inv

  nsmul_succ:= by
    intro n x
    dsimp
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    rw [← hx]
    have h1 : FreeExpRing.of (ExpRingTerm.base ((n + 1):ℕ )) * FreeExpRing.of x' = FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of x' + FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of x' := by
      have h1: FreeExpRing.of (ExpRingTerm.base (n + 1)) = FreeExpRing.of (ExpRingTerm.base n) + FreeExpRing.of (ExpRingTerm.base 1) := by
        apply Quotient.sound
        apply ExpRingTerm.Rel.add_hom
      zify
      rw[h1]
      rw[my_add_mul1]
    have h2: FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of x' = FreeExpRing.of x' := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.one_mul
    have h3: (FreeExpRing.of x')= ⟦x'⟧:=by
      rfl
    rw[← h3]
    rw[fuffa]
    rw[h1]
    rw[h2]
    simp
  zsmul_zero':= by
    intro x
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    have h1 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 * x := by
      rw [← hx]
      rfl
    rw [← hx]
    apply my_zero_mul
  zsmul_succ':= by
    intro n x
    dsimp
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    rw [← hx]
    have h1 : FreeExpRing.of (ExpRingTerm.base ((n + 1):ℕ )) * FreeExpRing.of x' = FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of x' + FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of x' := by
      have h1: FreeExpRing.of (ExpRingTerm.base (n + 1)) = FreeExpRing.of (ExpRingTerm.base n) + FreeExpRing.of (ExpRingTerm.base 1) := by
        apply Quotient.sound
        apply ExpRingTerm.Rel.add_hom
      zify
      rw[h1]
      rw[my_add_mul1]
    have h2: FreeExpRing.of (ExpRingTerm.base 1) * FreeExpRing.of x' = FreeExpRing.of x' := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.one_mul
    have h3: (FreeExpRing.of x')= ⟦x'⟧:=by
      rfl
    rw[← h3]
    rw[fuffa]
    rw[h1]
    rw[h2]
    simp
  zsmul_neg':=by
    intro n a
    dsimp
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    rw[fuffa]
    have h: (base (Int.negSucc n))=  (base (-(n+1))) := by
      rfl
    have h1: FreeExpRing.of (base (-(n+1))) =FreeExpRing.of (- (base (n+1))) :=by
      apply Quotient.sound
      apply ExpRingTerm.Rel.symm
      apply neg_scalar
    rw[h]
    rw[h1]
    apply Quotient.sound
    apply ExpRingTerm.Rel.symm
    apply my_mul_neg
    exact a'
    exact a'



#check FreeExpRing

instance : Algebra ℤ FreeExpRing where
  smul :=  fun n x => (FreeExpRing.of (ExpRingTerm.base n)) * x
  algebraMap := {
    toFun := fun n => FreeExpRing.of (ExpRingTerm.base n),
    map_one' := by
      dsimp
      rfl
    map_mul' := by
      intros x y
      dsimp
      apply Quotient.sound
      apply ExpRingTerm.Rel.mul_hom
    map_zero' := by
      dsimp
      rfl
    map_add' := by
      intros x y
      dsimp
      apply Quotient.sound
      apply ExpRingTerm.Rel.add_hom
  }
  commutes':=by
      intro n x
      dsimp
      let x' := x.exists_rep
      rcases x' with ⟨x', hx⟩
      rw [← hx]
      have h1 : FreeExpRing.of (ExpRingTerm.base n * x') = FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of x' := by
        rfl
      repeat rw[fuffa]
      rw[← h1]
      have h2: FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of x' = FreeExpRing.of x' * FreeExpRing.of (ExpRingTerm.base n) := by
        apply Quotient.sound
        apply ExpRingTerm.Rel.mul_comm
      rw[← h2]
      apply Quotient.sound
      apply ExpRingTerm.Rel.symm
      apply ExpRingTerm.Rel.refl

  smul_def':=by
      intro n x
      dsimp
      rfl

#check IsAlgebraic

open Polynomial

lemma ne_zero_of_eq_my (a : ℤ[X]): (a = X-3) →  a ≠ 0 := by
  intro h
  rw[h]
  apply support_nonempty.1
  use 1
  simp



/- instance: ToString ExpRingTerm where
  toString x:= match x with
              | (base (n : ℤ)) =>  (instToStringInt.toString n)
              | (add a b) => "(" ++ toString a ++ " + " ++ toString b ++ ")"
              | (mul a b) => "(" ++ toString a ++ " * " ++ toString b ++ ")"
              | (exp a) => "exp(" ++ toString a ++ ")"



theorem fuffa1: IsAlgebraic ℤ (FreeExpRing.of (ExpRingTerm.base 3)) :=by
  constructor
  constructor
  apply ne_zero_of_eq_my
  rfl
  simp
  have h:  (algebraMap ℤ FreeExpRing 3)= FreeExpRing.of (ExpRingTerm.base 3) := by
    rfl
  have h1: ((aeval (FreeExpRing.of (base (3:ℤ)))) (3: ℤ[X])) = (algebraMap ℤ FreeExpRing 3) :=by
    simp
 -/



@[simp]
noncomputable def expcast1  : (ExpRingTerm →  ℝ  ):=
(fun x => match x with
          |ExpRingTerm.base q => (q : ℝ)
          |ExpRingTerm.add a b => (expcast1 a) + (expcast1 b)
          |ExpRingTerm.mul a b => (expcast1 a) * (expcast1 b)
          |ExpRingTerm.exp a => Real.exp (expcast1 a))




@[simp]
noncomputable def expcast2 : (FreeExpRing → ℝ) :=
    Quotient.lift (expcast1) (by
      intro a b
      intro h
      induction h
      case add_fun  c d e f h1 h2  h3  h4 =>
        have h5: (expcast1 c) + (expcast1 d) = (expcast1 e) + (expcast1 f) := by
          rw[h3]
          rw[h4]
        have h6: (expcast1 (c + d))= (expcast1 c) + (expcast1 d):=by
          rfl
        rw[h6]
        rw[h5]
        rfl
      case mul_fun c d e f h1 h2  h3  h4 =>
        have h5: (expcast1 c) * (expcast1 d) = (expcast1 e) * (expcast1 f) := by
          rw[h3]
          rw[h4]
        have h6: (expcast1 (c * d))= (expcast1 c) * (expcast1 d):=by
          rfl
        rw[h6]
        rw[h5]
        rfl
      case exp_fun c d h1 h2 =>
        have h3: Real.exp (expcast1 c) = expcast1 (c.exp):= by
          rfl
        have h4: Real.exp (expcast1 d) = expcast1 (d.exp):= by
          rfl
        rw[← h3]
        rw[← h4]
        rw[h2]
      case refl=>
        rfl
      case symm a b h1 h2 =>
        rw[h2]
      case trans a b c h1 h2 h3 =>
        rw[h2]
        rw[h3]
      case add_comm c d =>
        have h1: (expcast1 c) + (expcast1 d) = (expcast1 d) + (expcast1 c) := by
          rw[add_comm]

        have h2: (expcast1 (c + d)) = (expcast1 c) + (expcast1 d) := by
          rfl
        rw[h2]
        rw[h1]
        rfl
      case add_assoc c d e =>
        have h1: (expcast1 c) + (expcast1 d) + (expcast1 e) = (expcast1 c) + ((expcast1 d) + (expcast1 e)) := by
          rw[add_assoc]
        have h2: (expcast1 (c + d + e)) = (expcast1 c) + (expcast1 d) + (expcast1 e) := by
          rfl
        rw[h2]
        rw[h1]
        rfl

      case mul_comm c d =>
        have h1: (expcast1 c) * (expcast1 d) = (expcast1 d) * (expcast1 c) := by
          rw[mul_comm]

        have h2: (expcast1 (c * d)) = (expcast1 c) * (expcast1 d) := by
          rfl
        rw[h2]
        rw[h1]
        rfl
      case mul_assoc c d e =>
        have h1: (expcast1 c) * (expcast1 d) * (expcast1 e) = (expcast1 c) * ((expcast1 d) * (expcast1 e)) := by
          rw[mul_assoc]
        have h2: (expcast1 (c * d * e)) = (expcast1 c) * (expcast1 d) * (expcast1 e) := by
          rfl
        rw[h2]
        rw[h1]
        rfl
      case add_zero c =>

        have h2: (expcast1 (base 0)) =  Int.cast 0 := by
            rfl
        have h3: (expcast1 (c+ base 0)) = (expcast1 c) + (expcast1 (base 0)) := by
          rfl
        rw[h3]
        rw[h2]
        have h4: (Int.cast 0) = (0:ℝ ) := by
          simp
        rw[h4]
        simp
      case zero_add c =>

        have h2: (expcast1 (base 0)) =  Int.cast 0 := by
            rfl
        have h3: (expcast1 (base 0 + c )) =  (expcast1 (base 0)) +(expcast1 c) := by
          rfl
        rw[h3]
        rw[h2]
        have h4: (Int.cast 0) = (0:ℝ ) := by
          simp
        rw[h4]
        simp
      case add_inv c =>
        have h2: (expcast1 (-c + c)) = (expcast1 (-c)) + (expcast1 c) := by
          rfl
        have h3: (expcast1 (-c)) = (expcast1 ((base (-1))*c)) := by
          rfl
        have h4: (expcast1 ((base (-1))*c)) = (expcast1 (base (-1))) * (expcast1 c) := by
          rfl
        have h5: (expcast1 (base (-1))) = Int.cast (-1) := by
          rfl
        have h6:   Int.cast (-1)  = (-1:ℝ) :=by
          simp
        rw[h2]
        rw[h3]
        rw[h4]
        rw[h5]
        rw[h6]
        simp
      case add_mul c d e =>
        have h2: (expcast1 ((c + d) * e)) = (expcast1 (c + d)) * (expcast1 e) := by
          rfl
        have h3: (expcast1 (c + d)) = (expcast1 c) + (expcast1 d) := by
          rfl
        have h4: ((expcast1 c + expcast1 d) * expcast1 e) = (expcast1 c) * (expcast1 e) + (expcast1 d) * (expcast1 e) := by
          apply add_mul
        rw[h2]
        rw[h3]
        rw[h4]
        rfl
      case exp_add c d=>
        have h2: (expcast1 (c + d)) = (expcast1 c) + (expcast1 d) := by
          rfl
        have h3: (Real.exp (expcast1 c + expcast1 d)) = (Real.exp (expcast1 c)) * (Real.exp (expcast1 d)) := by
          apply Real.exp_add
        have h4: (expcast1 (c + d).exp) = (expcast1 (c+d)).exp:= by
            rfl
        rw[h4]
        rw[h2]
        rw[h3]
        rfl
      case exp_zero =>
        have h2: (expcast1 (base 0)) =  Int.cast 0 := by
            rfl
        have h3: (Real.exp (expcast1 (base 0))) = (Real.exp (Int.cast 0)) := by
          rfl
        have h4: (expcast1 (base 0).exp) = (expcast1 (base 0)).exp:= by
            rfl
        rw[h4]
        rw[h2]
        have h5: (Int.cast 0) = (0:ℝ ) := by
          simp
        rw[h5]
        have h6: expcast1 (base 1) = Int.cast 1 := by
          rfl
        have h7: (Int.cast 1) = (1:ℝ ) := by
          simp
        rw[h6]
        rw[h7]
        simp
      case add_hom c d=>
        have h0: expcast1 (base (c) + base (d)) = (expcast1 (base c)) + (expcast1 (base d)) := by
          rfl
        have h1 (x:ℤ ): expcast1 (base (x)) = (x : ℝ) := by
          rfl
        rw[h0]
        rw[h1 c,h1 d, h1 (c+d)]
        simp
      case mul_hom c d=>
        have h0: expcast1 (base (c) * base (d)) = (expcast1 (base c)) * (expcast1 (base d)) := by
          rfl
        have h1 (x:ℤ ): expcast1 (base (x)) = (x : ℝ) := by
          rfl
        rw[h0]
        rw[h1 c,h1 d, h1 (c*d)]
        simp
      case one_mul c=>
        simp
      case mul_one c=>
        simp
      case mul_add a b c =>
        simp
        rw[mul_add]
    )


def FreeExpRing_Real := Set.range expcast2



@[simp]
noncomputable instance: ERing FreeExpRing_Real where
  base := λ n => ⟨expcast2 (FreeExpRing.of (base n)), by
    use FreeExpRing.of (base n)
    ⟩
  exp x:= ⟨Real.exp x.1, by
    rcases x.2 with ⟨a, ha⟩
    let a' := a.exists_rep
    rcases a' with ⟨a', ha'⟩
    use FreeExpRing.of (ExpRingTerm.exp a')
    have h: expcast2 (FreeExpRing.of a'.exp)= Real.exp (expcast2 (FreeExpRing.of a')) := by
      rfl
    rw[h]
    rw[← fuffa]
    rw[ha']
    rw[ha]
    ⟩

  add x y := ⟨x.1 + y.1,by
    rcases x.2 with ⟨a, ha⟩
    rcases y.2 with ⟨b, hb⟩
    let a' := a.exists_rep
    let b' := b.exists_rep
    rcases a' with ⟨a', ha'⟩
    rcases b' with ⟨b', hb'⟩
    use FreeExpRing.of (ExpRingTerm.add a' b')
    have h: expcast2 (FreeExpRing.of (a' + b')) = expcast2 (FreeExpRing.of a') + expcast2 (FreeExpRing.of b') := by
      rfl
    rw[← ha]
    rw[← hb]
    rw[fuffa] at ha'
    rw[fuffa] at hb'
    rw[← ha']
    rw[← hb']
    have h1: FreeExpRing.of (a' + b') = FreeExpRing.of (a'.add b') :=by
      rfl
    rw[← h1]
    rw[h]
  ⟩
  mul x y := ⟨x.1 * y.1,by
    rcases x.2 with ⟨a, ha⟩
    rcases y.2 with ⟨b, hb⟩
    let a' := a.exists_rep
    let b' := b.exists_rep
    rcases a' with ⟨a', ha'⟩
    rcases b' with ⟨b', hb'⟩
    use FreeExpRing.of (ExpRingTerm.mul a' b')
    have h: expcast2 (FreeExpRing.of (a' * b')) = expcast2 (FreeExpRing.of a') * expcast2 (FreeExpRing.of b') := by
      rfl
    rw[← ha]
    rw[← hb]
    rw[fuffa] at ha'
    rw[fuffa] at hb'
    rw[← ha']
    rw[← hb']
    have h1: FreeExpRing.of (a' * b') = FreeExpRing.of (a'.mul b') :=by
      rfl
    rw[← h1]
    rw[h]
    ⟩
  neg x := ⟨-x.1,by
    rcases x.2 with ⟨a, ha⟩
    let a' := a.exists_rep
    rcases a' with ⟨a', ha'⟩
    use FreeExpRing.of (-a')
    have h: expcast2 (FreeExpRing.of (-a')) = - expcast2 (FreeExpRing.of a') := by
      simp
    simp
    rw[← ha]
    rw[← ha']
    rw[fuffa]
    rfl
    ⟩
  zero := ⟨0,by
    use FreeExpRing.of (base 0)
    simp
    ⟩
  one := ⟨1,by
    use FreeExpRing.of (base 1)
    simp
    ⟩
  add_assoc := by
    intros
    apply Subtype.eq
    apply add_assoc
  add_comm := by
    intros
    apply Subtype.eq
    apply add_comm
  zero_add := by
    intros
    apply Subtype.eq
    apply zero_add
  add_zero := by
    intros
    apply Subtype.eq
    apply add_zero
  nsmul := fun n x => ⟨(n : ℝ) * x.1,by
    rcases x.2 with ⟨a, ha⟩
    let a' := a.exists_rep
    rcases a' with ⟨a', ha'⟩
    use FreeExpRing.of (base n * a')
    have h: expcast2 (FreeExpRing.of (base n * a')) = (n : ℝ) * expcast2 (FreeExpRing.of a') := by
      rfl
    rw[← ha]
    rw[← ha']
    rw[fuffa]
    rw[h]
    ⟩
  nsmul_zero := by
    intros
    simp
    apply Subtype.eq
    rfl
  nsmul_succ := by
    intros
    simp
    apply Subtype.eq
    simp
    rw[add_mul]
    rw[one_mul]
    rfl
  zsmul := fun n x => ⟨(n : ℝ) * x.1,by
    rcases x.2 with ⟨a, ha⟩
    let a' := a.exists_rep
    rcases a' with ⟨a', ha'⟩
    use FreeExpRing.of (base n * a')
    have h: expcast2 (FreeExpRing.of (base n * a')) = (n : ℝ) * expcast2 (FreeExpRing.of a') := by
      rfl
    rw[← ha]
    rw[← ha']
    rw[fuffa]
    rw[h]
    ⟩
  mul_comm :=by
    intros
    apply Subtype.eq
    apply mul_comm
  mul_assoc := by
    intros
    apply Subtype.eq
    apply mul_assoc
  one_mul := by
    intros
    apply Subtype.eq
    apply one_mul
  mul_one := by
    intros
    apply Subtype.eq
    apply mul_one
  left_distrib := by
    intros
    apply Subtype.eq
    apply left_distrib
  right_distrib := by
    intros
    apply Subtype.eq
    apply right_distrib
  zero_mul := by
    intros
    apply Subtype.eq
    apply zero_mul
  mul_zero := by
    intros
    apply Subtype.eq
    apply mul_zero
  zsmul_zero' := by
    intros
    simp
    apply Subtype.eq
    rfl
  zsmul_succ' := by
    intros
    simp
    apply Subtype.eq
    simp
    rw[add_mul]
    rw[one_mul]
    rfl
  zsmul_neg' := by
    intros
    apply Subtype.eq
    simp
    nth_rw 3 [← neg_one_mul]
    nth_rw 2[add_mul]
    rw[mul_add]
    rw[← mul_assoc,← mul_assoc]
    rw[add_mul ]
    ring
  neg_add_cancel := by
    intros
    apply Subtype.eq
    apply neg_add_cancel
  exp_zero := by
    intros
    apply Subtype.eq
    simp
  base_hom := by
    intro a b
    apply Subtype.eq
    simp
    rfl
  exp_hom := by
    intro a b
    apply Subtype.eq
    simp
    apply Real.exp_add


noncomputable instance: RingHom FreeExpRing ℝ  where
  toFun := expcast2
  map_one' := by
    have h: expcast2 (FreeExpRing.of (base 1)) = 1 := by
      simp
    exact h
  map_mul' := by
    intro a b
    let a' := a.exists_rep
    let b' := b.exists_rep
    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    simp
    rw[← ha]
    rw[← hb]
    repeat rw[fuffa]
    rfl
  map_add' := by
    intro a b
    let a' := a.exists_rep
    let b' := b.exists_rep
    rcases a' with ⟨a', ha⟩
    rcases b' with ⟨b', hb⟩
    simp
    rw[← ha]
    rw[← hb]
    repeat rw[fuffa]
    rfl
  map_zero' := by
    have h: expcast2 (FreeExpRing.of (base 0)) = 0 := by
      simp
    exact h
