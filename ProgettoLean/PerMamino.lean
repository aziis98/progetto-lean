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

lemma my_neg_add (a: ExpRingTerm) (b: ExpRingTerm) : (-(a + b)).Rel ((-a)+ (-b)) := by
  have h: (-(a + b)).Rel ((ExpRingTerm.base (-1))*(a + b)) := by
    apply ExpRingTerm.Rel.refl
  have h1: ExpRingTerm.Rel ((ExpRingTerm.base (-1)) * (a + b)) ((ExpRingTerm.base (-1)) * a + (ExpRingTerm.base (-1)) * b) := by
    apply ExpRingTerm.Rel.mul_add
  have h2: ExpRingTerm.Rel ((ExpRingTerm.base (-1)) * a + (ExpRingTerm.base (-1)) * b) ((-a) + (-b)) := by
    apply ExpRingTerm.Rel.refl
  apply ExpRingTerm.Rel.trans _ (base (-1) * (a + b)) _
  exact h
  apply ExpRingTerm.Rel.trans _ (base (-1) * a + base (-1) * b) _
  exact h1
  exact h2

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
    -- have h3
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

    dsimp

    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    rw [← hx]

    have h  : FreeExpRing.of (ExpRingTerm.base (n + 1 : ℕ)) = FreeExpRing.of (ExpRingTerm.base n) + FreeExpRing.of (ExpRingTerm.base 1) := by
      apply Quotient.sound
      zify
      apply ExpRingTerm.Rel.add_hom

    rw [h]

    have h1 : FreeExpRing.of x' = ⟦x'⟧ := by
      rfl

    rw [← h1]

    rw [my_add_mul]
    have h2: FreeExpRing.of (ExpRingTerm.base n) * FreeExpRing.of (x')= FreeExpRing.of (ExpRingTerm.base n * x') := by
      rfl

    rw [h2]

    have h3 : FreeExpRing.of (ExpRingTerm.base 1 * x') = FreeExpRing.of x' := by
      apply Quotient.sound
      apply ExpRingTerm.Rel.one_mul

    rw [h3]


noncomputable def my_neg :FreeExpRing → FreeExpRing := fun x => FreeExpRing.of (- Quotient.out x)

lemma my_neg_lemma1 (a' : ExpRingTerm) : my_neg (FreeExpRing.of a') = FreeExpRing.of (-a'):=
  by
    apply Quotient.sound
    have h: Quotient.out (FreeExpRing.of (a')) ≈ a' := by
      apply Quotient.exact
      apply Quotient.out_eq
    apply neg_fun
    exact h
lemma my_neg_lemma2 (a b c: ExpRingTerm) : (a.Rel b) → ((-a) + c).Rel (-b +c) := by
  intro h
  have h1: (-a).Rel (-b) := by
    apply neg_fun
    exact h
  have h2: (-a + c).Rel (-b + c) := by
    apply ExpRingTerm.Rel.add_fun
    exact h1
    apply ExpRingTerm.Rel.refl
  exact h2





lemma fuffa (a: ExpRingTerm) : ⟦a⟧ = FreeExpRing.of a := by
  rfl

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




noncomputable instance : Ring FreeExpRing where
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
  neg x:= my_neg x
  neg_add_cancel:= by
    intro a
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw[← ha]
    dsimp
    have h: my_neg ⟦a'⟧ =FreeExpRing.of (- a') := by
      dsimp
      have h1: ⟦a' ⟧=FreeExpRing.of a' := by
        rfl
      rw[h1]
      rw[← my_neg_lemma1]

    rw[h]
    have h1: ⟦a' ⟧=FreeExpRing.of a' := by
      rfl
    rw[h1]
    rw[← my_neg_lemma1]
    apply Quotient.sound
    have h2: Quotient.out (FreeExpRing.of a') ≈ a' := by
      apply Quotient.exact
      apply Quotient.out_eq
    have h3:- Quotient.out (FreeExpRing.of a') + a' ≈ -a' +a' := by
      apply my_neg_lemma2
      exact h2
    apply ExpRingTerm.Rel.trans _ ((-a') +a') _
    exact h3
    apply ExpRingTerm.Rel.add_inv
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
    rw[h1]
    rw[h2]



  zsmul_neg':= by
    intro n a
    dsimp
    let a' := a.exists_rep
    rcases a' with ⟨a', ha⟩
    rw [← ha]
    have h1 : ⟦a'⟧ =FreeExpRing.of a' := by
      rfl
    rw[h1]
    have h2: Int.negSucc n = -((n+1): ℤ  ) := by
      rfl
    rw[h2]


    have h3 :FreeExpRing.of (base (-(n+1))) * FreeExpRing.of a'= FreeExpRing.of ((base (-(n+1) )) * a') :=by
      rfl
    rw[h3]
    have h4: my_neg (FreeExpRing.of (base ↑(n + 1)) * FreeExpRing.of a')= FreeExpRing.of (-Quotient.out (FreeExpRing.of (base (n + 1)) * FreeExpRing.of a')):=by
      rfl
    rw[h4]
    apply Quotient.sound
    have h5: Quotient.out (FreeExpRing.of (base (n + 1))) ≈ base (n + 1) := by
      apply Quotient.exact
      apply Quotient.out_eq
    have h6: - base (n+1) ≈ base (- (n+1)) := by
      apply neg_scalar
    have h7: -Quotient.out (FreeExpRing.of (base (n + 1))) * a' ≈ -base (n + 1) * a' := by
      apply right_mul
      apply neg_fun
      exact h5
    have h8: - base (n+1) * a' ≈ base (- (n+1)) * a' := by
      apply right_mul
      exact h6
    apply ExpRingTerm.Rel.trans _ (-base ((↑n + 1)) * a') _
    exact h8.symm
    apply ExpRingTerm.Rel.trans _ (-Quotient.out (FreeExpRing.of (base (n + 1))) * a') _
    apply h7.symm
    have h9 :Quotient.out (FreeExpRing.of (base (↑n + 1)) * FreeExpRing.of a') ≈ Quotient.out (FreeExpRing.of (base (↑n + 1))) * Quotient.out (FreeExpRing.of a') :=by
      apply Quotient_mul
    have h10: Quotient.out (FreeExpRing.of a') ≈ a' := by
      apply Quotient.exact
      apply Quotient.out_eq
    have h11: Quotient.out (FreeExpRing.of (base (↑n + 1))) * Quotient.out (FreeExpRing.of a') ≈ Quotient.out (FreeExpRing.of (base (↑n + 1))) * a' := by
      apply left_mul
      exact h10
    have h12 :ExpRingTerm.Rel (- (Quotient.out (FreeExpRing.of (base (↑n + 1))) * Quotient.out (FreeExpRing.of a'))) (- (Quotient.out (FreeExpRing.of (base (↑n + 1))) * a')):= by
      apply neg_fun
      exact h11
    apply ExpRingTerm.Rel.trans _ (-(Quotient.out (FreeExpRing.of (base (↑n + 1))) * Quotient.out (FreeExpRing.of a'))) _


  /-  intro n x
    dsimp
    let x' := x.exists_rep
    rcases x' with ⟨x', hx⟩
    rw [← hx]
    have h1 : FreeExpRing.of x'= ⟦x'⟧ := by
      rfl
    have h2 :Int.negSucc n  = -((n+1): ℕ ) := by
      rfl
    rw[← h1]
    rw[h2]
    have  h3: FreeExpRing.of (base (-↑(n + 1)))= my_neg (FreeExpRing.of (base (n + 1)) ):= by
      apply Quotient.sound
      have h3: Quotient.out (FreeExpRing.of (base (n + 1))) ≈ base (n + 1) := by
        apply Quotient.exact
        apply Quotient.out_eq
      have h4: - base (n+1) ≈ base (- (n+1)) := by
        apply neg_scalar
      have h5: -Quotient.out (FreeExpRing.of (base (n + 1))) ≈ -base (n + 1):=by
        apply neg_fun
        exact h3
      apply ExpRingTerm.Rel.trans _ (-base (n + 1)) _
      exact h4.symm
      exact h5.symm
    rw[h3]
    apply Quotient.sound
    have h4: Quotient.out (FreeExpRing.of (base (n + 1))) ≈ base (n + 1) := by
      apply Quotient.exact
      apply Quotient.out_eq
    have h5: (Quotient.out (FreeExpRing.of (base (↑n + 1)))) * x'≈ base (n + 1) * x' := by
      apply right_mul
      exact h4
    have h6: - (Quotient.out (FreeExpRing.of (base (↑n + 1))) * x') ≈( - (base (n + 1) * x')) := by
      apply neg_fun
      exact h5
    have h7 : (Quotient.out (FreeExpRing.of (base (↑n + 1))) * x') ≈ (Quotient.out (FreeExpRing.of (base (↑n + 1)) * FreeExpRing.of x')):=by
      apply Quotient.exact
    -/




    -- have h2 : ExpRingTerm.base 0 * x' = ExpRingTerm.base 0 := by




    -- have h2 : ⟦ExpRingTerm.base 0 * x'⟧ = 0 := by





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
