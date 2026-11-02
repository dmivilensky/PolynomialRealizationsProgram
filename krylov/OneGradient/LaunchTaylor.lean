import krylov.OneGradient.LaunchFirstJet
import krylov.Stability.FirstOrderTaylor
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch, actual C2 full-window launch remainder.
Use: transfer the proved true semantic output derivative to the original
quadratic remainder directly from primitive smooth physical data.
Source: the genuine actual full observed inverse model, original operator
product regularity and the reused compact smooth Taylor theorem at a singleton reference.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Set krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine canonical full-window output has the printed launch
compression expansion with an actual quadratic remainder from primitive C2 data.
Use: the statement concerns the original observed coefficient solve, by
launch_semantic_coefficients, rather than an assumed regular output or model jet.
Article: main_krylov, prop:launch, canonical compression formula with O(omega^2).
Proof: primitive C2 observations derive actual model-inverse and semantic-output
C2 regularity. The true reference residual vanishes and the proved actual
launch derivative is the compression coefficient. Reuse the genuine compact
smooth Taylor estimate at the actual reference to obtain a true radius and constant. -/
theorem launch_semantic_quadratic_remainder
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : ℝ → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ 2 S 0) (hu : IsUnit (S 0).det)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContDiffAt ℝ 2 g 0) :
    let P := fun l => transportedFlag (metricRoot base*S 0) l
    let R := cgOperator (metricRoot base)⁻¹
    let D := ∑ l∈Finset.range n,cgOperator (P l)ᵀ*
      (R*(deriv (fun t => cgOperator (A t (l+1))) 0-deriv (fun t => cgOperator (A t l)) 0)*R)*cgOperator (P l)
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (launchSemanticGradient (S t) (A t) (g t))+t • D (R (g 0))‖≤C*t^2 := by
  let R := cgOperator (metricRoot base)⁻¹
  let Phi := fun t => R (launchSemanticGradient (S t) (A t) (g t))
  let D := ∑ l∈Finset.range n,cgOperator (transportedFlag (metricRoot base*S 0) l)ᵀ*
    (R*(deriv (fun t => cgOperator (A t (l+1))) 0-deriv (fun t => cgOperator (A t l)) 0)*R)*
      cgOperator (transportedFlag (metricRoot base*S 0) l)
  have hinv := launch_model_inverse_contDiff base hb S hS hu A hA hA0
  have hquery := (matrixOperator_contDiffAt _ 0 hinv).clm_apply hg
  have houtput := hg.sub ((matrixOperator_contDiffAt _ 0 (hA n)).clm_apply hquery)
  have hPhi : ContDiffAt ℝ 2 Phi 0 := R.contDiff.contDiffAt.comp 0 houtput
  have hJ0 : launchObservedModel (S 0) (A 0)=base := by
    rw [show A 0=(fun _ => base) from funext hA0]
    exact launch_model_reference base (S 0) hb.1.isSymm hu
  have hcancel : cgOperator base (cgOperator base⁻¹ (g 0))=g 0 := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb.det_pos.ne'),map_one,one_apply_eq_self]
  have hzero : Phi 0=0 := by
    change R (g 0-cgOperator (A 0 n) (cgOperator (launchObservedModel (S 0) (A 0))⁻¹ (g 0)))=0
    rw [hA0,hJ0,hcancel,sub_self,map_zero]
  have hjet := launch_semantic_first_jet base hb S (hS.of_le (by norm_num)) hu A
    (fun k => (hA k).of_le (by norm_num)) hsym hA0 g (hg.of_le (by norm_num))
  change HasDerivAt Phi (-(D (R (g 0)))) 0 at hjet
  obtain ⟨delta,C,hd,hC,hbound⟩ := c2_first_order_remainder Phi (-(D (R (g 0)))) hPhi hjet
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht
  simpa only [hzero,sub_zero,smul_neg,sub_neg_eq_add] using hbound t ht

end
end krylov.OneGradient
