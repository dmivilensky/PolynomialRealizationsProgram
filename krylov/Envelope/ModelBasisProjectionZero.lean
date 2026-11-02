import krylov.Methods.ProbedModelReference
import krylov.Envelope.ExploredFlag

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine full-model and canonical projection cancellation.
Use: turn actual physical reference-model coordinate cancellation into zero true explored canonical output variation.
Source: genuine CG-consistent current-direction scaling, actual recorded CG steps, real primal/dual metric pairing and the true finite orthonormal flag projection.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator BigOperators
variable {n : ℕ}

/-- A real vector orthogonal to the actual full CG reference model has zero genuine explored inverse-root projection.
Use: A real vector orthogonal to the actual full CG reference model has zero genuine explored inverse-root projection.
Article: main_krylov, apB:prop:consist, genuine full-model and canonical projection cancellation.
Proof: Recover every actual CG step from the true current direction and chronological old basis, move the real metric pairing and apply the genuine orthonormal prefix projection formula. -/
theorem explored_projection_zero_of_modelBasis (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (v : EuclideanSpace ℝ (Fin n))
    (hzero : ∀ j : Fin (k+1),inner ℝ
      (probedStepBasis m (fun _ => cgOperator base) (fun _ => cgOperator base) g k j) v=0) :
    (exploredFlag base g (k+1)).starProjection (cgOperator (metricRoot base)⁻¹ v)=0 := by
  have hQ := cgOperator_positive base hb
  -- The genuine current direction and reversed actual old-step coordinates cover every true CG reference step.
  have hs (i : ℕ) (hi : i<k+1) : inner ℝ (referenceStep (cgOperator base) g i) v=0 := by
    by_cases he : i=k
    · subst i
      have hh := hzero 0
      obtain ⟨c,hc,hd,_⟩ := hm (cgOperator base) hQ.1 hQ.2 g k
      change inner ℝ (m.direction (methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) v=0 at hh
      rw [hd,real_inner_smul_left] at hh
      have hz : inner ℝ (CG.direction (cgOperator base) g k) v=0 := (mul_eq_zero.mp hh).resolve_left hc.ne'
      rw [referenceStep,real_inner_smul_left,hz,mul_zero]
    · have hik : i<k := by omega
      have hh := hzero (Fin.succ (⟨k-1-i,by omega⟩ : Fin k))
      change inner ℝ (probedStep m (fun _ => cgOperator base) (fun _ => cgOperator base) g (k-1-(k-1-i))) v=0 at hh
      rw [show k-1-(k-1-i)=i by omega,quadratic_probedStep_eq_cg m hm _ hQ.1 hQ.2] at hh
      exact hh
  -- Real primal/dual metric pairing turns all genuine physical step coordinates into zero actual canonical projection coordinates.
  rw [exploredFlag_projection base hb g hcount]
  apply Finset.sum_eq_zero
  intro i _
  have hi : inner ℝ (canonicalCGUnitStep base g i.val) (cgOperator (metricRoot base)⁻¹ v)=0 := by
    change inner ℝ (‖canonicalCGStep base g i.val‖⁻¹ • canonicalCGStep base g i.val)
      (cgOperator (metricRoot base)⁻¹ v)=0
    rw [real_inner_smul_left]
    have hp := canonical_search_pairing base hb (referenceStep (cgOperator base) g i.val) v
    change inner ℝ (referenceStep (cgOperator base) g i.val) v=
      inner ℝ (canonicalCGStep base g i.val) (cgOperator (metricRoot base)⁻¹ v) at hp
    rw [← hp,hs i.val i.isLt,mul_zero]
  rw [hi,zero_smul]
end
end krylov.Envelope
