import jacobi.Finite.Gram
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.WithLp

/-!
Article: jacobi, Proposition 1.1.
Gram--Schmidt depends real-analytically on analytic input vectors wherever the
input family is independent. This supplies the analytic reconstruction step
instead of treating smoothness of the spectral-weight chart as an assumption.
Source: finite Gram--Schmidt and the elementary analytic calculus in mathlib.
Use: constructs analytic logarithmic spectral weight coordinates.
-/

namespace jacobi.Finite.AnalyticGram
noncomputable section
open InnerProductSpace Real Filter
open scoped InnerProductSpace Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ordinary real exponential is real-analytic at every argument.
Use: constructs analytic logarithmic spectral weight coordinates.
Article: jacobi, Proposition 1.1.
Proof: identify the ordinary exponential with the existing Banach-algebra exponential. -/
theorem exp_analytic (x : ℝ) : AnalyticAt ℝ Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.exp_analytic x

/-- The positive square-root branch is real-analytic.
Use: normalizes Gram residuals and positive spectral weights analytically.
Article: jacobi, Proposition 1.1.
Proof: locally write sqrt y as exp(log y / 2) on the open positive half-line. -/
theorem sqrt_analytic {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have hl : AnalyticAt ℝ (fun y : ℝ => Real.log y * (1/2 : ℝ)) x :=
    (analyticAt_log hx).mul analyticAt_const
  have h : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y * (1/2 : ℝ))) x :=
    (exp_analytic _).comp hl
  apply h.congr
  filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

/-- A real Hilbert inner product of two analytic vector maps is analytic.
Use: handles all Gram entries, projection coefficients and squared residual norms.
Article: jacobi, Proposition 1.1.
Proof: compose the existing continuous bilinear inner product with the two maps. -/
theorem inner_analytic {f g : D → E} {x : D} (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => inner ℝ (f y) (g y)) x :=
  ((innerSL ℝ).analyticAt_bilinear _).comp (hf.prod hg)

/-- Norm is analytic along an analytic vector map at a nonzero vector.
Use: proves analyticity of the positive Gram--Schmidt normalization.
Article: jacobi, Proposition 1.1.
Proof: compose the positive square root with the analytic squared norm. -/
theorem norm_analytic {f : D → E} {x : D} (hf : AnalyticAt ℝ f x) (hx : f x ≠ 0) :
    AnalyticAt ℝ (fun y => ‖f y‖) x := by
  have hp : 0 < inner ℝ (f x) (f x) := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hs : AnalyticAt ℝ (fun y : D => inner ℝ (f y) (f y)) x := inner_analytic hf hf
  have h : AnalyticAt ℝ (fun y : D => Real.sqrt (inner ℝ (f y) (f y))) x :=
    (sqrt_analytic hp).comp (f := fun y : D => inner ℝ (f y) (f y)) hs
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using h

/-- Every unnormalized Gram residual is analytic at an independent input family.
Use: proves the analytic finite spectral reconstruction rather than assuming it.
Article: jacobi, Proposition 1.1.
Proof: induction over the finite ordered input; all projection denominators are
nonzero squared norms, and each preceding residual is analytic by induction. -/
theorem residual_analytic {N : ℕ} (f : D → Fin N → E) {x : D}
    (hf : ∀ i, AnalyticAt ℝ (fun y => f y i) x) (hi : LinearIndependent ℝ (f x)) (i : Fin N) :
    AnalyticAt ℝ (fun y => gramSchmidt ℝ (f y) i) x := by
  -- Only earlier residuals occur in the projection sum, and independence makes their norm denominators nonzero.
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin N → Fin N → Prop)).induction with
  | h i ih =>
    have hs : AnalyticAt ℝ (fun y => ∑ j ∈ Finset.Iio i,
        (inner ℝ (gramSchmidt ℝ (f y) j) (f y i) / ‖gramSchmidt ℝ (f y) j‖^2) •
          gramSchmidt ℝ (f y) j) x := by
      apply Finset.analyticAt_fun_sum
      intro j hj
      have hj' := ih j (Finset.mem_Iio.mp hj)
      have hn := inner_analytic hj' hj'
      simp only [real_inner_self_eq_norm_sq] at hn
      exact ((inner_analytic hj' (hf i)).div hn
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j hi)))).smul hj'
    have he : (fun y => gramSchmidt ℝ (f y) i) =
        (fun y => f y i - ∑ j ∈ Finset.Iio i,
          (inner ℝ (gramSchmidt ℝ (f y) j) (f y i) / ‖gramSchmidt ℝ (f y) j‖^2) •
            gramSchmidt ℝ (f y) j) := by
      funext y
      rw [gramSchmidt_def]
      simp only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
    rw [he]
    exact (hf i).sub hs

/-- The normalized Gram--Schmidt vectors are analytic at independent inputs.
Use: supplies the actual orthonormal polynomial basis in the analytic weight chart.
Article: jacobi, Proposition 1.1.
Proof: divide each analytic residual by its nonzero analytic norm. -/
theorem normalized_analytic {N : ℕ} (f : D → Fin N → E) {x : D}
    (hf : ∀ i, AnalyticAt ℝ (fun y => f y i) x) (hi : LinearIndependent ℝ (f x)) (i : Fin N) :
    AnalyticAt ℝ (fun y => gramSchmidtNormed ℝ (f y) i) x := by
  have h := residual_analytic f hf hi i
  have hn := norm_analytic h (gramSchmidt_ne_zero i hi)
  have hp := (hn.inv (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hi))).smul h
  change AnalyticAt ℝ (fun y => ‖gramSchmidt ℝ (f y) i‖⁻¹ • gramSchmidt ℝ (f y) i) x at hp
  simpa only [gramSchmidtNormed, RCLike.ofReal_real_eq_id, id_eq] using hp

end
end jacobi.Finite.AnalyticGram
