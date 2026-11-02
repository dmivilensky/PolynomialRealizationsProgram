import krylov.Cancellation.DeferredSharp
import krylov.Envelope.CorrectionFreeHiddenPrefix
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, universal original correction-free budget witness.
Use: construct one genuine symmetric source increment family forcing the
whole sum-budget last-energy first variation on every original CG-consistent
correction-free method, without assuming a method response or smoothness.
Source: actual exact hidden-prefix execution, genuine CG orthonormal prefixes,
real symmetric planar matrices and true physical/canonical metric cancellation.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- One real symmetric original budget scenario, chosen independently of the
method, forces the full sum-budget fresh first variation on every genuine
CG-consistent correction-free executor.
Use: the calibrated DC upper bound is therefore the actual correction-free
first-order minimax value; no regularity or response assumption is needed for
this universal witness's real exact executed source path.
Article: main_krylov, thm:DC, W0 times square-root last energy lower bound.
Proof: align all genuine source increments between the actual first and last
CG unit steps. Every earlier true probe defect vanishes, while their final
combined action is the sum of the actual budgets times the common first step.
The existing exact hidden-prefix execution gives the real affine output for
all methods; cancel the true metric root and differentiate that actual path. -/
theorem correction_free_budget_witness
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 0<k) (hcount : k+1≤referenceAtomCount base hb g)
    (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin n)),CGConsistent m → Methods.CorrectionFree m →
      ∀ B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      HasDerivAt (fun t => cgOperator (metricRoot base)⁻¹ (probedGradient m (canonicalFCPath base E t) (B t) g (k+1)))
        ((Real.sqrt (cgEnergy base g k)*(∑ l∈range k,omega l)) • canonicalCGUnitStep base g 0) 0 := by
  let e := canonicalCGUnitStep base g 0
  let h := canonicalCGUnitStep base g k
  let E := fun l => planarMatrix e h 0 (omega l) 0
  let W := ∑ l∈range k,omega l
  have hframe := canonicalCGUnitStep_orthonormal base hb g (k+1)
    (fun j hj => cg_nonstagnation base hb g j (hj.trans_le hcount))
  have hGram := orthonormal_iff_ite.mp hframe
  have hpair (i j : ℕ) (hi : i<k+1) (hj : j<k+1) (hne : i≠j) :
      inner ℝ (canonicalCGUnitStep base g i) (canonicalCGUnitStep base g j)=0 := by
    have hp := hGram ⟨i,hi⟩ ⟨j,hj⟩
    have hneFin : (⟨i,hi⟩ : Fin (k+1))≠⟨j,hj⟩ := fun he => hne (congrArg Fin.val he)
    rw [ite_eq_right hneFin] at hp
    exact hp
  have heh : inner ℝ e h=0 := hpair 0 k (by omega) (by omega) (by omega)
  have hhe : inner ℝ h e=0 := (real_inner_comm _ _).trans heh
  have hhh : inner ℝ h h=1 := by
    have hh := hGram ⟨k,by omega⟩ ⟨k,by omega⟩
    simpa only [ite_true] using hh
  have hlast : cgOperator (∑ l∈range k,E l) h=W • e := by
    rw [cgOperator,map_sum,_root_.sum_apply]
    change (∑ l∈range k,cgOperator (E l) h)=_
    rw [show W • e=∑ l∈range k,omega l • e from Finset.sum_smul]
    apply sum_congr rfl
    intro l _
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h 0 (omega l) 0) h=_
    rw [planarMatrix_action,heh,hhh]
    simp only [mul_zero,mul_one,add_zero,zero_add,zero_smul]
  have hprefix : ∀ j<k,cgOperator (∑ l∈range j,E l) (canonicalCGUnitStep base g j)=0 := by
    intro j hj
    rw [cgOperator,map_sum,_root_.sum_apply]
    apply sum_eq_zero
    intro l hl
    have hj0 : 0<j := by have := mem_range.mp hl;omega
    have hej := hpair 0 j (by omega) (by omega) (by omega)
    have hhj := hpair k j (by omega) (by omega) (by omega)
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h 0 (omega l) 0) (canonicalCGUnitStep base g j)=0
    rw [planarMatrix_action,hej,hhj]
    simp only [mul_zero,add_zero,zero_smul]
  have horth : inner ℝ h (cgOperator (∑ l∈range k,E l) h)=0 := by
    rw [hlast,real_inner_smul_right,hhe,mul_zero]
  refine ⟨E,fun _ => planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · intro l hl
    have hn := (deferred_cross_increment base hb g k l hl hcount 0 (omega l) (homega l hl)).2.1
    change ‖planarMatrix (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g k) 0 (omega l) 0‖≤omega l
    simpa only [deferredTail,zero_smul,zero_add,canonicalCGUnitStep] using hn
  · intro m hm hfree B
    let V := cumulativeDrift base E k (referenceStep (cgOperator base) g k)
    let R := cgOperator (metricRoot base)⁻¹
    have hpath (t : ℝ) : R (probedGradient m (canonicalFCPath base E t) (B t) g (k+1))=
        cgCanonicalError base g (k+1)+t • ((Real.sqrt (cgEnergy base g k)*W) • e) := by
      rw [correctionFree_hidden_prefix_gradient m hm hfree base hb g E k (by omega) hprefix horth (B t) t,map_add,map_smul]
      have hmetric := canonical_drift_action base (∑ l∈range k,E l) hb (referenceStep (cgOperator base) g k)
      change R V=cgOperator (∑ l∈range k,E l) (canonicalCGStep base g k) at hmetric
      have hs : canonicalCGStep base g k=Real.sqrt (cgEnergy base g k) • h := by
        rw [cgEnergy_sqrt base hb]
        exact (NormedSpace.norm_smul_normalize _).symm
      rw [hmetric,hs,map_smul,hlast,smul_smul]
      change cgCanonicalError base g (k+1)+(t*Real.sqrt (cgEnergy base g k)) • (W • e)=
        cgCanonicalError base g (k+1)+t • ((Real.sqrt (cgEnergy base g k)*W) • e)
      module
    have hd : HasDerivAt (fun t : ℝ => cgCanonicalError base g (k+1)+t • ((Real.sqrt (cgEnergy base g k)*W) • e))
        ((Real.sqrt (cgEnergy base g k)*W) • e) 0 := by
      simpa only [id_eq,one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const ((Real.sqrt (cgEnergy base g k)*W) • e)).const_add (cgCanonicalError base g (k+1))
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hpath)

end
end krylov.Cancellation
