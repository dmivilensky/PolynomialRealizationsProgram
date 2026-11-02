import jacobi.Support.EdgeWaveBound
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: mathlib, Complex.norm_cderiv_le.
Use: naturalWave_edge_derivative applies the community Cauchy estimate to the same actual support wave used in the original edge and Gram comparisons.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual original complex support wave is complex differentiable on the entire spectral plane.
Use: naturalWave_edge_derivative applies the community Cauchy estimate to the same actual support wave used in the original edge and Gram comparisons.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: mathlib, differentiability of polynomial evaluation.
Proof: the actual real polynomial's complex algebraic evaluation is the ordinary evaluation of its complex coefficient-map polynomial. -/
theorem naturalWave_differentiable (a b:ℝ) (ha:-1<a) (hb:-1<b) (n m:ℕ) :
    Differentiable ℂ (naturalWave a b ha hb n m) := by
  change Differentiable ℂ (fun z => Polynomial.eval₂ (algebraMap ℝ ℂ) z (naturalPolynomial a b ha hb n m))
  simpa only [Polynomial.eval_map] using
    ((naturalPolynomial a b ha hb n m).map (algebraMap ℝ ℂ)).differentiable

/-- The genuine original support wave has the complete local n^2 spectral-derivative bound throughout every fixed complex scaled-energy endpoint disc.
Use: the original support interpolation estimates at fixed edge indices have an actual derivative bound for the same original polynomial; the full frequency envelope must further control growing indices away from this bounded energy region.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: Cauchy's derivative estimate, mathlib Complex.norm_cderiv_le.
Proof: center a genuine circle of radius n^(-2) at the original energy. It stays in the proved endpoint disc with its radius enlarged from R to R+1. The actual polynomial is entire, so Cauchy's estimate divides its original power bound by this exact radius, giving the stated n^2 factor. -/
theorem naturalWave_edge_derivative {a b:ℝ} (ha:-1<a) (hb:-1<b) {R:ℝ} (hR:0≤R) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+4→∀y:ℂ,
      ‖y-1‖≤R/(n:ℝ)^2→
        ‖deriv (naturalWave a b ha hb n m) y‖≤C*(n:ℝ)^2*((m:ℝ)+1)^gamma a := by
  -- The original energy disc is enlarged by exactly the genuine Cauchy radius; no derivative or envelope certificate is assumed.
  obtain ⟨C,hC,hbound⟩ := naturalWave_near_one ha hb (R:=R+1) (by positivity)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro m hm y hy
  have hn0 : (0:ℝ)<n := by exact_mod_cast hnpos
  have hr : 0<1/(n:ℝ)^2 := by positivity
  have hcircle (z:ℂ) (hz:z∈Metric.sphere y (1/(n:ℝ)^2)) :
      ‖naturalWave a b ha hb n m z‖≤C*((m:ℝ)+1)^gamma a := by
    apply hn m hm z
    have hzy : ‖z-y‖=1/(n:ℝ)^2 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
    calc
      _ ≤ ‖z-y‖+‖y-1‖ := by simpa only [dist_eq_norm] using dist_triangle z y (1:ℂ)
      _ ≤ 1/(n:ℝ)^2+R/(n:ℝ)^2 := add_le_add hzy.le hy
      _ = _ := by ring
  have hd : DifferentiableOn ℂ (naturalWave a b ha hb n m) univ :=
    (naturalWave_differentiable a b ha hb n m).differentiableOn
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  exact (Complex.norm_cderiv_le hr hcircle).trans_eq (by field_simp)

end
end jacobi.Support
