import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.InnerProductSpace.L2Space
import Mathlib.Data.Real.Basic

open Real MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable (I B : ℝ × ℝ → ℝ)

noncomputable section

-- Treat ℝ² as Euclidean space
abbrev ℝ² := EuclideanSpace ℝ (Fin 2)

-- Assume I and B are differentiable scalar fields over ℝ²
variable (I B : ℝ² → ℝ)

-- Gradient of a scalar field at a point
def grad (f : ℝ² → ℝ) (x : ℝ²) : ℝ² :=
  (∇ f) x  -- This uses mathlib's gradient operator


def residual (p : ℝ) : ℝ :=
  ∫ x, ‖grad (fun x ↦ I x - p • B x) x‖ ^ 2 ∂volume



def residual (p : ℝ) : ℝ :=
  ∫ x, ‖∇ (I x - p • B x)‖ ^ 2 ∂volume


theorem optimal_p :
  let num := ∫ x, ⟪∇ (I x), ∇ (B x)⟫ ∂volume
  let denom := ∫ x, ‖∇ (B x)‖ ^ 2 ∂volume
  denom ≠ 0 →
  ArgMinOn residual ℝ (fun p ↦ p = num / denom)



noncomputable def R (p : ℝ) : ℝ :=
  ∫ (x : ℝ × ℝ), ‖∇ (I x - p • B x)‖^2 ∂volume


-- import Mathlib.Data.Nat.Basic

-- open Nat

--theorem add_zero (n : ℕ) : n + 0 = n := by
--  induction n with
--  | zero => rfl
--  | succ n ih => simp [ih]

--example : 1 + 0 = 1 := add_zero 1


import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

open scoped BigOperators

-- Define a pixel as a pair of natural numbers
abbrev Pixel := ℕ × ℕ

-- Gradient is a 2D vector at each pixel
abbrev Gradient := Pixel → ℝ × ℝ

-- Dot product of two gradients over a finite domain ∈
def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let fx := f x
    let gx := g x
    fx.1 * gx.1 + fx.2 * gx.2

-- Cost function R(p) = ||∇I - p ∇B||² over the domain
def R (∇I ∇B : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot ∇I ∇I D - 2 * p * gradDot ∇B ∇I D + p ^ 2 * gradDot ∇B ∇B D

-- Optimal p that minimizes R
def p_opt (∇I ∇B : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot ∇I ∇B D / gradDot ∇B ∇B D



----------------

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped BigOperators

abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂

def R (∇I ∇B : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot ∇I ∇I D - 2 * p * gradDot ∇B ∇I D + p ^ 2 * gradDot ∇B ∇B D

def p_opt (∇I ∇B : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot ∇I ∇B D / gradDot ∇B ∇B D

lemma R_has_minimum_at_p_opt
  (∇I ∇B : Gradient) (D : Finset Pixel)
  (h : gradDot ∇B ∇B D ≠ 0) :
  ∀ p : ℝ, R ∇I ∇B D p ≥ R ∇I ∇B D (p_opt ∇I ∇B D) := by
  let a := gradDot ∇B ∇B D
  let b := gradDot ∇B ∇I D
  let c := gradDot ∇I ∇I D
  have ha : 0 < a := by
    -- Since a = sum of squared norms of ∇B, and h ≠ 0, we assume it's positive
    -- You can strengthen this with a lemma if needed
    sorry
  intro p
  let p₀ := b / a
  let R' := fun p ↦ c - 2 * p * b + p ^ 2 * a
  have : R ∇I ∇B D p = R' p := rfl
  have : R ∇I ∇B D p₀ = R' p₀ := rfl
  calc
    R' p = a * (p - p₀) ^ 2 + (c - b ^ 2 / a) := by
      ring_nf
      field_simp [h]
      ring
    _ ≥ c - b ^ 2 / a := by
      apply add_le_add_right
      apply mul_self_nonneg
  done
----------------

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped BigOperators

-- A pixel is just a pair of coordinates
abbrev Pixel := ℕ × ℕ

-- A Gradient is a function from a pixel to a 2D real vector
abbrev Gradient := Pixel → ℝ × ℝ

-- Dot product of two gradients over a finite domain
def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂

-- Quadratic cost function R(p) = ||∇I - p ∇B||² over domain D
def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D

-- Optimal value of p that minimizes R
noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D

-- Proof that p_opt minimizes R under the assumption the denominator is positive
lemma R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : a ≠ 0 := ne_of_gt h
  intro p
  let p₀ := b / a
  let Rp := fun p ↦ a * (p - p₀)^2 + (c - b^2 / a)
  have hRp : R dI dB D p = Rp p := by
    field_simp [ha]
    ring
  have hRp_opt : R dI dB D (p_opt dI dB D) = Rp p₀ := by
    field_simp [ha]
    ring
  rw [hRp, hRp_opt]
  apply add_le_add_right
  exact mul_self_nonneg _


------------


import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped BigOperators

abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂

def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D

noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D

lemma R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : a ≠ 0 := ne_of_gt h
  intro p
  let p₀ := b / a
  let Rp := fun p ↦ a * (p - p₀)^2 + (c - b^2 / a)
  have hRp : R dI dB D p = Rp p := by
    field_simp [ha]
    ring
  have hRp_opt : R dI dB D (p_opt dI dB D) = Rp p₀ := by
    field_simp [ha]
    ring
  rw [hRp, hRp_opt]
  apply add_le_add_right
  exact mul_self_nonneg _


---------------------


import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped BigOperators

abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂

def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D

noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D

lemma R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : a ≠ 0 := ne_of_gt h
  intro p
  let p₀ := b / a
  let Rp := fun p ↦ a * (p - p₀)^2 + (c - b^2 / a)
  have hRp : R dI dB D p = Rp p := by
    field_simp [ha]
    ring
  have hRp_opt : R dI dB D (p_opt dI dB D) = Rp p₀ := by
    field_simp [ha]
    ring
  rw [hRp, hRp_opt]
  apply add_le_add_right
  exact mul_self_nonneg _


---------------


import analysis.calculus.deriv
import data.real.basic

open real

example (a b c : ℝ) (h : 0 < a) :
  ∃ x₀ : ℝ, ∀ x : ℝ, a * x ^ 2 + b * x + c ≥ a * x₀ ^ 2 + b * x₀ + c :=
begin
  let f := λ x : ℝ, a * x ^ 2 + b * x + c,
  have deriv_f : deriv f = λ x, 2 * a * x + b,
  { ext x,
    simp [f, deriv_add, deriv_mul_const, deriv_id'],
    ring },
  let x₀ := -b / (2 * a),
  use x₀,
  intro x,
  have H : deriv f x₀ = 0,
  { rw [deriv_f, ←sub_eq_zero, ←eq_sub_iff_add_eq],
    field_simp [ne_of_gt h],
    ring },
  have f_diff : differentiable ℝ f := by continuity,
  exact convex_on_real_iff_deriv2_nonneg.mpr
    ⟨f, f_diff, λ x, by simp [f, mul_nonneg (le_of_lt h) (by norm_num)]⟩ x x₀,
end

----------

scope = "leanprover-community"

-------------


import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic

open Real

noncomputable def quad (a b c : ℝ) (x : ℝ) : ℝ :=
  a * x ^ 2 + b * x + c

lemma quadratic_has_minimum (a b c : ℝ) (h : 0 < a) :
    ∃ x₀ : ℝ, ∀ x, quad a b c x₀ ≤ quad a b c x := by
  let x₀ := -b / (2 * a)
  use x₀
  intro x
  have : quad a b c x = a * (x - x₀) ^ 2 + quad a b c x₀ := by
    rw [quad, ←sub_sq, ←mul_add, ←add_assoc]
    ring
  rw [this]
  apply add_le_add_right
  exact mul_nonneg h.le (pow_two_nonneg _)

--------------

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic

open Real

-- Define the quadratic function
def quadratic (a b c x : ℝ) : ℝ := a * x^2 + b * x + c

-- Now prove that it has a minimum when a > 0
theorem quadratic_has_minimum {a b c : ℝ} (h : 0 < a) :
  ∃ x₀, ∀ x, quadratic a b c x₀ ≤ quadratic a b c x :=
by
  let x₀ := -b / (2 * a)
  use x₀
  intro x
  -- Complete the square
  have : quadratic a b c x = a * (x + b / (2 * a))^2 + (c - b^2 / (4 * a)) := by
    field_simp [quadratic]
    ring
  rw [this]
  have : quadratic a b c x₀ = a * (x₀ + b / (2 * a))^2 + (c - b^2 / (4 * a)) := by
    field_simp [quadratic]
    ring
  rw [this]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left
  · apply sq_nonneg
  · linarith

--------------------------------


import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.GoldenRatio -- Not strictly needed for this proof but often imported with Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic -- For `has_deriv_at`

open Real

def quadratic (a b c x : ℝ) : ℝ := a * x^2 + b * x + c

theorem quadratic_has_minimum {a b c : ℝ} (h : 0 < a) :
  ∃ x₀, ∀ x, quadratic a b c x₀ ≤ quadratic a b c x :=
by
  -- The quadratic function is differentiable.
  have h_diff : Differentiable ℝ (fun x => quadratic a b c x) := by
    apply Differentiable.add
    apply Differentiable.add
    exact (differentiable_const _).mul (differentiable_id.pow 2)
    exact (differentiable_const _).mul differentiable_id
    exact differentiable_const _

  -- Calculate the derivative of the quadratic function.
  have deriv_quadratic (x : ℝ) : deriv (fun y => quadratic a b c y) x = 2 * a * x + b := by
    simp [quadratic]
    rw [deriv_add_const (a * x^2 + b * x) c]
    rw [deriv_add_const (a * x^2) (b * x)]
    rw [deriv_mul_const_left (x^2) a]
    rw [deriv_pow_const 2 x]
    rw [deriv_mul_const_left x b]
    simp [deriv_id]

  -- Find the x-coordinate of the vertex by setting the derivative to zero.
  let x₀ := -b / (2 * a)

  -- Show that the derivative is zero at x₀.
  have deriv_at_x₀ : deriv (fun x => quadratic a b c x) x₀ = 0 := by
    rw [deriv_quadratic]
    field_simp [x₀]
    ring

  -- Use the first derivative test. Since `a > 0`, the parabola opens upwards,
  -- so the critical point is a minimum.
  use x₀
  intro x

  -- We need to show `quadratic a b c x₀ ≤ quadratic a b c x`.
  -- This is equivalent to `quadratic a b c x - quadratic a b c x₀ ≥ 0`.
  -- Let's expand this difference.
  have diff_val : quadratic a b c x - quadratic a b c x₀ = a * (x - x₀)^2 := by
    simp only [quadratic]
    have : a * x^2 + b * x + c - (a * x₀^2 + b * x₀ + c) = a * (x^2 - x₀^2) + b * (x - x₀) := by
      ring
    rw [this]
    have : x^2 - x₀^2 = (x - x₀) * (x + x₀) := by rw [sq_sub_sq]
    rw [this]
    have : x₀ = -b / (2 * a) := rfl
    have : b = -2 * a * x₀ := by field_simp [this]; ring
    rw [this]
    calc
      a * ((x - x₀) * (x + x₀)) + (-2 * a * x₀) * (x - x₀)
        = a * (x - x₀) * (x + x₀) - 2 * a * x₀ * (x - x₀) := by ring
      _ = a * (x - x₀) * (x + x₀ - 2 * x₀) := by rw [← mul_sub_right_distrib]
      _ = a * (x - x₀) * (x - x₀) := by ring
      _ = a * (x - x₀)^2 := by rw [mul_self_eq_pow_two]

  -- Now we use the fact that `a > 0` and `(x - x₀)^2 ≥ 0`.
  calc
    quadratic a b c x₀ ≤ quadratic a b c x := by
      rw [← sub_nonneg]
      rw [diff_val]
      apply mul_nonneg
      exact le_of_lt h
      exact pow_two_nonneg (x - x₀)

----------------------

import Mathlib.Analysis.Calculus.Deriv

open Real

example : deriv (fun x => x ^ 2) 3 = 6 := by
  simp [deriv]

----------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.GoldenRatio -- Not strictly needed for this proof but often imported with Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic -- For `has_deriv_at`
import Mathlib.Analysis.Calculus.Deriv.Basic

open Real

def quadratic (a b c x : ℝ) : ℝ := a * x^2 + b * x + c

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]


theorem foo_bar (a b : ℝ) : -a + (a + b) = b := by
  trace_state
  rw [← add_assoc]
  trace_state
  rw [neg_add_cancel]
  trace_state
  rw [zero_add]


theorem bar_foo (a b : ℝ) : a + b + -b = a := by
  aesop

theorem quadratic_has_minimum {a b c : ℝ} (h : 0 < a) :
  ∃ x₀, ∀ x, quadratic a b c x₀ ≤ quadratic a b c x := by
  sorry

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))

---------------------

--import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Tactic

open Real

theorem quadratic_has_minimum (a b c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, a * x ^ 2 + b * x + c ≥ a * x₀ ^ 2 + b * x₀ + c := by
  -- Let x₀ be the vertex of the parabola
  let x₀ := -b / (2 * a)
  use x₀
  intro x
  -- Rewrite the quadratic in completed square form
  have h : a * x ^ 2 + b * x + c =
           a * (x + b / (2 * a)) ^ 2 - b ^ 2 / (4 * a) + c := by
    ring
  rw [h]
  -- The square term is ≥ 0 since a > 0
  have sq_nonneg : 0 ≤ (x + b / (2 * a)) ^ 2 := by apply sq_nonneg
  have a_pos : 0 ≤ a := le_of_lt ha
  have term_nonneg : 0 ≤ a * (x + b / (2 * a)) ^ 2 := mul_nonneg a_pos sq_nonneg
  --linarith

-------------------

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology

-- Define the quadratic function
def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

theorem quadratic_monotonicity {a b c : ℝ} (h : 0 < a) :
  MonotoneOn (quadratic a b c) (Ici (-b / (2 * a))) ∧
  AntitoneOn (quadratic a b c) (Iic (-b / (2 * a))) := by
  -- Use derivative to determine monotonicity
  have deriv_quadratic : ∀ x, HasDerivAt (quadratic a b c) (2 * a * x + b) x := by
    intro x
    simp only [quadratic]
    convert (hasDerivAt_id x).pow 2 |>.const_mul a |>.add ((hasDerivAt_id x).const_mul b)
    ring
  constructor
  · -- Monotone on [−b/2a, ∞)
    exact convexOn_id.comp_monotoneOn
      (fun x _ => (deriv_quadratic x).deriv) (convex_Ici _)
      (by intro x hx; simp [mul_assoc, h, add_nonneg_iff]; linarith)
  · -- Antitone on (−∞, −b/2a]
    exact convexOn_id.comp_antitoneOn
      (fun x _ => (deriv_quadratic x).deriv) (convex_Iic _)
      (by intro x hx; simp [mul_assoc, h, add_nonpos_iff]; linarith)


-------------------------

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Set Filter Topology

-- Define the quadratic function
def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

-- Prove monotonicity on [−b/(2a), ∞) when a > 0
theorem quadratic_monotone_right {a b c : ℝ} (h : 0 < a) :
    MonotoneOn (quadratic a b c) (Ici (-b / (2 * a))) := by
  intros x y hx
  simp only [quadratic]
  -- We'll use the derivative: f'(x) = 2a x + b
  have deriv : ∀ x, HasDerivAt (quadratic a b c) (2 * a * x + b) x := by
    intro x
    simp only [quadratic]
    convert (hasDerivAt_id x).pow 2 |>.const_mul a |>.add ((hasDerivAt_id x).const_mul b)
    ring
  -- Since a > 0, the derivative is ≥ 0 on [−b/(2a), ∞)
  have nonneg_deriv : ∀ x ∈ Ici (-b / (2 * a)), 0 ≤ 2 * a * x + b := by
    intro x hx
    have : x + b / (2 * a) ≥ 0 := by
      field_simp [ne_of_gt h] at hx
      linarith
    calc
      2 * a * x + b = 2 * a * (x + b / (2 * a)) - b + b := by
        field_simp [ne_of_gt h]
        ring
      _ ≥ 0 := by
        nlinarith [h, this]
  -- Now apply the Mean Value Theorem
  exact convexOn_id.comp_monotoneOn
    (fun x _ => (deriv x).deriv) (convex_Ici _) nonneg_deriv

----------------


def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

theorem quadratic_monotone_right {a b c : ℝ} (h : 0 < a) :
    MonotoneOn (quadratic a b c) (Ici (-b / (2 * a))) := by
  intros x y hx
  simp only [quadratic]
  trace_state
  have deriv : ∀ x, HasDerivAt (quadratic a b c) (2 * a * x + b) x := by
    intro x
    simp only [quadratic]
    convert (hasDerivAt_id x).pow 2 |>.const_mul a |>.add ((hasDerivAt_id x).const_mul b)
    ring

    sorry



import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

def quadratic (a k c x : ℝ) : ℝ := a * (x - k) ^ 2 + c

theorem quadratic_has_minimum (a k c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, a * (x - k) ^ 2 + c ≥ a * (x₀ - k)^ 2 + c := by
    sorry


-----------------------

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology


def quadratic (a k c x : ℝ) : ℝ := a * (x - k) ^ 2 + c

theorem quadratic_has_minimum (a k c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic a k c x ≥ quadratic a k c x₀ := by
  use k
  intro x
  unfold quadratic
  calc
    a * (x - k) ^ 2 + c ≥ 0 + c := by
      apply add_le_add_right
      apply mul_nonneg
      exact le_of_lt ha
      exact sq_nonneg (x - k)
    _ = a * (k - k) ^ 2 + c := by
      rw [sub_self, pow_two, mul_zero, zero_add]

------------------------

theorem quadratic_has_minimum (a b c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic a b c x ≥ quadratic a b c x₀ := by
  -- Let h = -b / (2a), k = c - b^2 / (4a)
  let h := -b / (2 * a)
  let k := c - b ^ 2 / (4 * a)
  -- Show that the standard form equals the vertex form with these h and k
  have h_eq : ∀ x, quadratic a b c x = quadratic_vertex a h k x := by
    intro x
    unfold quadratic quadratic_vertex
    -- Expand the vertex form: a * (x - h)^2 + k
    -- = a * (x^2 - 2hx + h^2) + k
    -- = a * x^2 - 2a * h * x + a * h^2 + k
    -- Substitute h = -b / (2a), k = c - b^2 / (4a)
    have : h = -b / (2 * a) := rfl
    have : k = c - b ^ 2 / (4 * a) := rfl
    field_simp [this]
    ring
  -- Apply the vertex form minimum theorem
  obtain ⟨x₀, hx₀⟩ := vertex_quadratic_has_minimum a h k ha
  use x₀
  intro x
  rw [h_eq x, h_eq x₀]
  exact hx₀ x


------------------------------

lemma quadratic_eq_vertex_form (a b c : ℝ) (ha : a ≠ 0) :
    ∀ x, quadratic a b c x = quadratic_vertex a (-b / (2 * a)) (c - b ^ 2 / (4 * a)) x := by
  intro x
  unfold quadratic quadratic_vertex
  -- Expand the vertex form: a * (x + b/(2a))^2 + (c - b^2/(4a))
  -- = a * (x^2 + (b/a)x + b^2/(4a^2)) + (c - b^2/(4a))
  -- = a * x^2 + b * x + c
  have h1 : (x - (-b / (2 * a))) ^ 2 = x ^ 2 + (b / a) * x + (b ^ 2) / (4 * a ^ 2) := by
    field_simp [ha]
    ring
  rw [h1]
  field_simp [ha]
  ring

------------------------------


theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
    ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  -- Use the fact that the vertex form has a minimum at h
  have h_min : ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k h :=
    by
      intro x
      -- This is a direct application of your earlier theorem
      exact (vertex_quadratic_has_minimum a h k ha).elim (λ _ hx => hx x)
  intro p
  rw [h_eq p, h_eq h]
  exact h_min p


---------------------

theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
    ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  -- Define vertex parameters
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  -- Use equivalence between standard and vertex form
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  -- Use the known minimum of the vertex form at x = h
  have h_min : ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k h :=
    (vertex_quadratic_has_minimum a h k ha).choose_spec
  intro p
  rw [h_eq p, h_eq h]
  exact h_min p

---------------------


theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
    ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  -- Let h and k be the vertex parameters
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  -- Use the vertex form equivalence
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  -- Use the minimum property of the vertex form
  obtain ⟨p₀, hp₀⟩ := vertex_quadratic_has_minimum a h k ha
  -- We know the minimum occurs at x = h
  have p₀_eq : p₀ = h := by
    -- From the proof of vertex_quadratic_has_minimum, we used `use h`
    rfl
  intro p
  rw [h_eq p, h_eq p₀, p₀_eq]
  exact hp₀ p



------------------------------------------
lemma quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
  ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  intro p
  have h_eq := quadratic_eq_vertex_form a b c (ne_of_gt ha)
  rw [h_eq p, h_eq (-b / (2 * a))]
  -- Now we have: a * (p - h)^2 + k ≥ a * (h - h)^2 + k
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_sq : 0 ≤ (p - h)^2 := sq_nonneg _
  have h_nonneg : 0 ≤ a * (p - h)^2 := mul_nonneg (le_of_lt ha) h_sq

  linarith



---------------------
theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
  ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by


---------------------


lemma R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : a ≠ 0 := ne_of_gt h
  intro p
  let p₀ := b / a
  let Rp := fun p ↦ a * (p - p₀)^2 + (c - b^2 / a)
  have hRp : R dI dB D p = Rp p := by
    field_simp [ha]
    ring
  have hRp_opt : R dI dB D (p_opt dI dB D) = Rp p₀ := by
    field_simp [ha]
    ring
  rw [hRp, hRp_opt]
  apply add_le_add_right
  exact mul_self_nonneg _

---------------------

theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
  ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by

---------------------


#check (fderiv (x : ℝ), x^n) rewrite_by fun_trans


example (x : ℝ) :
    deriv (fun x ↦ 3 * x^2 + 2 * x) x = 6 * x + 2 := by
  -- We will break down the derivative using linearity.
  rw [deriv_add]
  -- Now we have two terms to differentiate. Let's handle the first one: deriv (fun x => 3 * x ^ 2) x
  rw [deriv_const_mul_self_pow]
  -- The second term: deriv (fun x => 2 * x) x
  rw [deriv_const_mul_id]
  -- Simplify the expressions
  simp
  -- Now the goal should be an equality that is arithmetically true.
  ring



/-
example (x : ℝ) :
    deriv (fun x ↦ 3 * x^2 + 2 * x) x = 6 * x + 2 := by
  -- Rewrite the function as a sum of two parts
  have h : (fun x ↦ 3 * x^2 + 2 * x) = (fun x ↦ 3 * x^2) + (fun x ↦ 2 * x) := by
    funext x; ring
  rw [h]
  apply deriv_add
  · exact (differentiable_const.mul differentiable_id).deriv
  · exact (differentiable_const.mul differentiable_id).deriv

-/


/-
example : deriv (fun x => x^2 + 3 * x) = fun x => 2 * x + 3 :=
  by funext x; exact deriv_add (deriv_pow _ _) (deriv_const_mul _ _)
-/

----------------------
example (x : ℝ) :
    deriv (fun y ↦ 3 * y^2 + 3 * y) x = 6 * x + 3 := by

  have h_diff1 : DifferentiableAt ℝ (fun y ↦ 3 * y ^ 2) x := by
    sorry

  have h_diff2 : DifferentiableAt ℝ (fun y ↦ 3 * y) x := by
    sorry

  trace_state
  rw [deriv_add h_diff1 h_diff2]


---------------------------------------


example (x : ℝ) :
    deriv (fun y ↦ 3 * y^2 + 3 * y) x = 6 * x + 3 := by

  have h_eq : (fun y ↦ 3 * y^2 + 3 * y) = (fun y ↦ 3 * y^2) + (fun y ↦ 3 * y) := by
    ext y
    ring

  congr
  rw [h_eq]


  have h_diff1 : DifferentiableAt ℝ (fun y ↦ 3 * y ^ 2) x := by
    --simp_all only [differentiableAt_const, differentiableAt_id', DifferentiableAt.pow, DifferentiableAt.mul]
    sorry

  have h_diff2 : DifferentiableAt ℝ (fun y ↦ 3 * y) x := by
    --simp only [differentiableAt_const_mul, differentiableAt_id]
    --simp only [DifferentiableAt.fun_const_smul]
    sorry


  rw [deriv_add h_diff1 h_diff2]

  have h1 : deriv (fun y ↦ 3 * y ^ 2) x = 6 * x := by
    sorry

  have h2 : deriv (fun y ↦ 3 * y) x = 3 := by
    rw [deriv_const_mul]
    simp [deriv_id']
    norm_num


  rw [h1, h2]

--------------


example (x : ℝ) :
    deriv (fun y ↦ 3 * y^2 + 3 * y) x = 6 * x + 3 := by
  let f := (fun y ↦ 3 * y^2)
  let g := (fun y ↦ 3 * y)

  have h_diff1 : DifferentiableAt ℝ f x := by
    -- `simp` uses `differentiableAt_const_mul` and `differentiableAt_pow`
    simp

  -- Proof for h_diff2: Differentiability of g (3 * y)
  have h_diff2 : DifferentiableAt ℝ g x := by
    -- `simp` uses `differentiableAt_const_mul` and `differentiableAt_id`
    simp

  -- Now, the goal is `deriv (fun y ↦ 3 * y^2 + 3 * y) x = 6 * x + 3`.
  -- We need to rewrite the function `(fun y ↦ 3 * y^2 + 3 * y)` to `f + g`.
  -- The `conv` tactic allows us to rewrite *inside* an expression.
  conv =>
    lhs -- Focus on the left-hand side of the main goal
    arg 1 -- Focus on the first argument of `deriv`, which is the function `(fun y ↦ ...)`
    ext y -- Enter function extensionality mode: introduce `y` to work on the function body
    -- Now the sub-goal in `conv` mode is `3 * y ^ 2 + 3 * y = f y + g y`
    -- This is definitionally true because `f y = 3 * y^2` and `g y = 3 * y`.
    rfl -- Prove this definitional equality

  -- After the `conv` block, the main goal has been transformed to:
  -- `deriv (f + g) x = 6 * x + 3`
  -- Now `deriv_add` can be applied because the pattern matches.
  rw [deriv_add h_diff1 h_diff2]

  -- The goal is now `deriv f x + deriv g x = 6 * x + 3`.

  -- Proof for h1: deriv f x = 6 * x
  have h1 : deriv f x = 6 * x := by
    unfold f -- Unfold `f` to its definition `(fun y ↦ 3 * y^2)`
    rw [deriv_const_mul]
    rw [deriv_pow 2]
    norm_num -- Simplifies `3 * (2 * x ^ 1)` to `6 * x`
    rfl

  -- Proof for h2: deriv g x = 3
  have h2 : deriv g x = 3 := by
    unfold g -- Unfold `g` to its definition `(fun y ↦ 3 * y)`
    rw [deriv_const_mul]
    rw [deriv_id'] -- Simplifies `deriv (fun y ↦ y) x` to `1`
    norm_num -- Simplifies `3 * 1` to `3`
    rfl

  -- Substitute `h1` and `h2` into the main goal.
  -- The goal is `(deriv f x) + (deriv g x) = 6 * x + 3`.
  -- After `rw [h1, h2]`, it becomes `(6 * x) + 3 = 6 * x + 3`.
  rw [h1, h2]

  -- Final proof by reflexivity.
  rfl


-----------------------------------


  /-
  -- 1. Apply the derivative of a sum.
  -- The derivative of f(y) + g(y) is deriv f(y) + deriv g(y).
    trace_state
    rw [deriv_add]
    sorry


  -- Now the goal is:
  -- deriv (fun y ↦ 3 * y ^ 2) x + deriv (fun y ↦ 3 * y) x = 6 * x + 3
  trace_state
  -- 2. Handle the first term: deriv (fun y ↦ 3 * y^2) x
  -- Use `deriv_const_mul` to pull out the constant 3.
  rw [deriv_const_mul]
  -- Now the goal is:
  -- 3 * deriv (fun y ↦ y ^ 2) x + deriv (fun y ↦ 3 * y) x = 6 * x + 3
  trace_state
  -- Use `deriv_pow` for the derivative of y^2 (which is 2y).
  rw [deriv_pow 2]

  -- Note: `deriv_pow` requires a natural number exponent.
  -- This will simplify `deriv (fun y ↦ y ^ 2) x` to `2 * x ^ (2 - 1)`, i.e., `2 * x`.
  -- Now the goal is:
  -- 3 * (2 * x ^ (2 - 1)) + deriv (fun y ↦ 3 * y) x = 6 * x + 3
  -- Simplify the exponent (2 - 1)
  norm_num -- This will simplify 2 - 1 to 1, and 3 * (2 * x) to 6 * x.
  -- Now the goal is:
  -- 6 * x + deriv (fun y ↦ 3 * y) x = 6 * x + 3
  trace_state
  -- 3. Handle the second term: deriv (fun y ↦ 3 * y) x
  -- Again, use `deriv_const_mul` to pull out the constant 3.
  rw [deriv_const_mul]
  -- Now the goal is:
  -- 6 * x + 3 * deriv (fun y ↦ y) x = 6 * x + 3
  trace_state
  -- Use `deriv_id` for the derivative of y (which is 1).
  simp [deriv_id']
  -- Now the goal is:
  -- 6 * x + 3 * 1 = 6 * x + 3
  trace_state

  norm_num

  trace_state

  norm_num
  trace_state

-/

  /-
  -- 4. Final simplification.
  norm_num -- This will simplify 3 * 1 to 3.
  -- Now the goal is:
  -- 6 * x + 3 = 6 * x + 3
  trace_state
  -- 5. The two sides are identical, so we can close the goal.
  ring -- Reflexivity.
-/




/-
theorem R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : 0 < a := h
  apply quadratic_minimizer a b c ha
  --apply quadratic_minimizer a (-2 * b) c ha
-/
--------------------------------------


example (x : ℝ) :
    deriv (fun y ↦ 3 * y^2 + 3 * y) x = 6 * x + 3 := by

  have ah1 : deriv (fun y ↦ 3 * y ^ 2) x = 6 * x := by
    rw [deriv_const_mul]
    trace_state
    rw [deriv_pow 2]
    trace_state
    simp?

  have ah2 : deriv (fun y ↦ 3 * y) x = 3 := by
    sorry

  rw [deriv_add, ah1, ah2]

----------------------------------------


lemma poly_diff_example (x : ℝ) : deriv (fun y ↦ 3 * y ^ 2 + 2 * y) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ (fun y ↦ 3 * y ^ 2) x := by
    apply DifferentiableAt.const_mul
    apply differentiableAt_fun_id.pow
  have h2 : DifferentiableAt ℝ (fun y ↦ 2 * y) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id
  convert deriv_add h1 h2
  trace_state
  conv =>
    lhs
    rw [deriv_const_mul]
    rw [deriv_pow 2]
  conv =>
    rhs
    rw [deriv_const_mul]
    rw [deriv_id']
  ring

-------------------------------------------

lemma poly_diff_example_foo (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  -- The derivative of a sum is the sum of the derivatives.
  rw [deriv_add]
  -- Apply the constant multiple rule and power rule for the first term.
  rw [deriv_const_mul, deriv_pow_const]
  -- Apply the constant multiple rule and identity rule for the second term.
  rw [deriv_const_mul, deriv_id']
  -- Simplify the constants.
  simp

------------------------------------------------

lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ (f) x := by
    apply DifferentiableAt.const_mul
    apply differentiableAt_fun_id.pow
  have h2 : DifferentiableAt ℝ (g) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id

  have h_sq : DifferentiableAt ℝ (fun x ↦ x ^ 2) x := by
    exact DifferentiableAt.pow differentiableAt_id 2

  have h_id : DifferentiableAt ℝ (fun x ↦ x) x := differentiableAt_id

  rw [deriv_add h1 h2]
  trace_state
  unfold f g
  trace_state
  rw [ deriv_const_mul 3 ]
  trace_state
  rw [deriv_pow 2 ]
  trace_state
  ring
  trace_state
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_mul, deriv_id'', one_mul, deriv_const', mul_zero, add_zero]
  trace_state
  ring_nf
  trace_state


-----------------------------------------------------

lemma poly_diff_example_1 (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ (f) x := by
    unfold f
    fun_prop
  have h2 : DifferentiableAt ℝ (g) x := by
    unfold g
    fun_prop

  rw [deriv_add h1 h2]
  unfold f g
  rw [ deriv_const_mul 3 ]
  rw [deriv_pow 2 ]
  ring
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_mul, deriv_id'', one_mul, deriv_const', mul_zero, add_zero]
  trace_state
  ring_nf
  trace_state


--------------------------------------------

-- https://proofassistants.stackexchange.com/questions/5157/derivative-of-polynomial-in-lean4

lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ (f) x := by
    apply DifferentiableAt.const_mul
    apply differentiableAt_fun_id.pow
  have h2 : DifferentiableAt ℝ (g) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id

  have h_sq : DifferentiableAt ℝ (fun x ↦ x ^ 2) x := by
    exact DifferentiableAt.pow differentiableAt_id 2
  rw [deriv_add h1 h2]
  unfold f g
  rw [ deriv_const_mul 3 ]
  rw [deriv_pow 2 ]
  ring
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_mul, deriv_id'', one_mul, deriv_const', mul_zero, add_zero]
  trace_state
  ring_nf
  trace_state



--------------------------------------------

  rw [deriv_const_mul 2 (differentiableAt_id x)]

  rw [deriv_const_mul, deriv_pow 2]
  rw [deriv_const_mul, deriv_id']
  rw [deriv_id]




--------------------------------------------


lemma poly_diff_example (x : ℝ) : deriv (fun y ↦ 3 * y ^ 2 + 2 * y) x = 6 * x + 2:= by
  have h1 : DifferentiableAt ℝ (fun y ↦ 3 * y ^ 2) x := by
    sorry
  have h2 : DifferentiableAt ℝ (fun y ↦ 2 * y ) x := by
    sorry
  rw [←deriv_add (fun y ↦ 3 * y ^ 2) (fun y ↦ 2 * y)  h1 h2]


--------------------------------------------

  rw [deriv_add (diff_pow_two x) ]
  rw [←diff_pow_two_const x]
  rw [deriv_const_mul]
  rw [deriv_id']
  ring
  apply differentiableAt_id
  apply diff_pow_two_const



--------------------------------------------

example (x : ℝ) : deriv (fun y ↦ 3 * y ^ 2) x = 6 * x := by


  rw [deriv_const_mul]
  trace_state

  have diffh : DifferentiableAt ℝ (fun y ↦ y ^ 2) x := by
    sorry

  rw [deriv_pow 2]
  trace_state
  ring


--------------------------------------------



--def f(x: ℝ) := 3 * x ^ 2
--def g(x: ℝ) := 2 * x

lemma diff_distr (x : ℝ) : deriv ( fun y ↦ 3 * y ^ 2 + 2 * y ) x = deriv ( fun y ↦ 3 * y ^ 2 ) x + deriv ( fun y ↦ 2 * y ) x := by
  --exact deriv_add (λ y, 3 * y ^ 2) (λ y, 2 * y) x,
  let f := fun y ↦ 3 * y ^ 2
  let g := fun y ↦ 2 * y

  have h1 (x : ℝ) : DifferentiableAt ℝ f x := by
    exact differentiable_at.const_mul 3 (differentiable_at_id'.pow 2)

  have h2 (x : ℝ) : DifferentiableAt ℝ g x := by
    exact differentiable_at.const_mul 2 differentiable_at_id'

  --rw [←function.add_apply f g, deriv_add h1 h2]
  sorry

 --------------------------------------------


lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ f x := by
    apply DifferentiableAt.const_mul
    exact DifferentiableAt.pow differentiableAt_id 2

  have h2 : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id

  rw [deriv_add h1 h2]
  unfold f g
  rw [deriv_const_mul, deriv_const_mul]
  rw [deriv_pow 2]
  trace_state
  simp?
  trace_state
  ring
  trace_state

--------------------------------------------

lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ f x := by
    --apply DifferentiableAt.const_mul
    --exact DifferentiableAt.pow differentiableAt_id 2
    unfold f
    fun_prop
  have h2 : DifferentiableAt ℝ g x := by
    --apply DifferentiableAt.const_mul
    --exact differentiableAt_id
    unfold g
    fun_prop

  rw [deriv_add h1 h2]
  unfold f g
  ring
  simp only [differentiableAt_fun_id, DifferentiableAt.fun_pow, differentiableAt_const,
    deriv_fun_mul, deriv_fun_pow'', Nat.cast_ofNat, Nat.reduceSub, pow_one, deriv_id'', mul_one,
    deriv_const', mul_zero, add_zero, one_mul]
  ring

--------------------------------------------


theorem R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : 0 < a := h
  apply quadratic_minimizer a b c ha
  --apply quadratic_minimizer a (-2 * b) c ha

--------------------------------------------

theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
    ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  have h_min := vertex_quadratic_minimizer a h k ha
  intro p
  rw [h_eq p, h_eq h]
  exact h_min p

--------------------------------------------


fun p =>
      calc
        R dI dB D p
          = c - 2 * p * beta + p ^ 2 * a        := by rw [R_eq p]
      _ = quadratic a b c p                     := by rw [rhs_eq_quad p]
      _ ≥ quadratic a b c (p_opt dI dB D)       := by
        have p_opt_eq : p_opt dI dB D = -b / (2 * a) := by
          rw [p_opt, hb]
          field_simp [hz]
        rw [p_opt_eq]
        apply quadratic_minimum
        exact hz

---------------------------------------------
