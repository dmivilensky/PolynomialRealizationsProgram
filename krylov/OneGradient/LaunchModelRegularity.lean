import krylov.OneGradient.LaunchModelJet
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch, primitive regularity of the actual full observed model.
Use: derive the genuine model and inverse regularity from original smooth
physical columns and segment data, on independently proved reference domains.
Source: original latest observed entries, the true finite spectral coordinate
equivalence and smooth inversion on the actual matrix unit group.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {r : WithTop ℕ∞}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual full observed model of constant quadratic segment data is
the original real reference operator in physical coordinates.
Use: derive the corrector reference value without assuming any desired output or model jet.
Article: main_krylov, prop:launch.
Proof: actual constant-operator secants give the true physical Gram model;
its latest symmetric selection changes nothing, and both actual full-column
inverse coordinate matrices cancel on their genuine nonsingular domains. -/
theorem launch_model_reference (base S : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.IsSymm) (hu : IsUnit S.det) :
    launchObservedModel S (fun _ => base)=base := by
  have hy : pairImages S (fun _ => base)=base*S := by ext i j;rfl
  have hG : (Sᵀ*base*S).IsSymm := by
    simp only [Matrix.IsSymm,transpose_mul,transpose_transpose,hb.eq,Matrix.mul_assoc]
  have ht : IsUnit Sᵀ.det := by simpa only [Matrix.det_transpose] using hu
  rw [launchObservedModel,hy,← Matrix.mul_assoc,latest_eq_of_isSymm hG]
  unfold inverseCongruence
  calc
    _ = (Sᵀ⁻¹*Sᵀ)*base*(S*S⁻¹) := by noncomm_ring
    _ = base := by rw [Matrix.nonsing_inv_mul _ ht,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul,Matrix.mul_one]

/-- Original C-r columns and physical segment matrices give a C-r true
chronological latest-information model and a C-r true ambient physical model.
Use: actual launch smoothness comes from primitive observations at the genuine
full-column inverse domain, including arbitrary nonconjugate moving data.
Article: main_krylov, prop:launch; lem:U.
Proof: each actual selected latest entry is a true compressed segment matrix
entry at its chronological newer index. Primitive products give all actual
C-r entries; the reused finite spectral coordinate equivalence assembles them.
The genuine column inverse and its transpose then give the actual ambient inverse congruence. -/
theorem launch_model_contDiff
    (S : X → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ r S 0) (hu : IsUnit (S 0).det)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ r (fun t => A t k) 0) :
    ContDiffAt ℝ r (fun t => latest ((S t)ᵀ*pairImages (S t) (A t))) 0 ∧
      ContDiffAt ℝ r (fun t => launchObservedModel (S t) (A t)) 0 := by
  let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)).toContinuousLinearEquiv
  have hSt : ContDiffAt ℝ r (fun t => (S t)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hS
  have hH : ContDiffAt ℝ r (fun t => latest ((S t)ᵀ*pairImages (S t) (A t))) 0 := by
    apply contDiff_spectral_matrix
    intro i j
    have hm := (hSt.mul (hA (max i j).val)).mul hS
    have hc := (matrixEntryEquiv n n).toContinuousLinearMap.contDiff.contDiffAt.comp 0 hm
    have hentry := contDiffAt_pi.mp hc (min i j,max i j)
    convert hentry using 1
    funext t
    rw [← observed_compression]
    rfl
  have hi := contDiff_spectral_inverse S 0 hS hu
  have hit : ContDiffAt ℝ r (fun t => ((S t)⁻¹)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hi
  refine ⟨hH,?_⟩
  simpa only [launchObservedModel,inverseCongruence,Matrix.transpose_nonsing_inv] using (hit.mul hH).mul hi

/-- The actual ambient observed inverse model is C-r from the original primitive
data at a true positive quadratic reference.
Use: the derivative of the actual corrector requires no supplied smooth model or inverse field.
Article: main_krylov, prop:launch.
Proof: the actual model is C-r by the primitive observation theorem; constant
quadratic reference observations derive its exact original positive reference
value, which supplies the genuine inverse domain for smooth inversion. -/
theorem launch_model_inverse_contDiff
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : X → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ r S 0) (hu : IsUnit (S 0).det)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ r (fun t => A t k) 0) (hA0 : ∀ k,A 0 k=base) :
    ContDiffAt ℝ r (fun t => (launchObservedModel (S t) (A t))⁻¹) 0 := by
  have hmodel := (launch_model_contDiff S hS hu A hA).2
  have he : launchObservedModel (S 0) (A 0)=base := by
    rw [show A 0=(fun _ => base) from funext hA0]
    exact launch_model_reference base (S 0) hb.1.isSymm hu
  apply contDiff_spectral_inverse _ 0 hmodel
  rw [he]
  exact isUnit_iff_ne_zero.mpr hb.det_pos.ne'

end
end krylov.OneGradient
