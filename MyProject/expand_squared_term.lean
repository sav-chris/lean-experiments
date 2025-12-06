import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1))


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


--set_option diagnostics true

lemma expand_squared_term_nd {n : ℕ}
    -- May need to use I B : EuclideanSpace ℝ (Fin n) → ℝ

    --(I B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    --∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • ⟪fderiv ℝ I x, fderiv ℝ B x⟫_ℝ + (ρ^2) • ‖(fderiv ℝ B x)‖^2

    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) * (fderiv ℝ B x) (EuclideanSpace.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }


    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u) (EuclideanSpace.single i 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single i 1))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (EuclideanSpace.single x_1 1) • (fderiv ℝ B x) (EuclideanSpace.single x_1 1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • u (EuclideanSpace.single x_1 1) • (c x_1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, (x i) • (x i))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, (x i) • (y i))
                simp only [Norm.norm]
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i))
                        * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                --simp only [mul_assoc]
                sorry
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring

    unfold inner
    trace_state



}



noncomputable def custom_inner_product
    {n : ℕ }
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    --(x : EuclideanSpace ℝ (Fin n))
:=
    (∑ i, u (EuclideanSpace.single i 1) * v (EuclideanSpace.single i 1))
