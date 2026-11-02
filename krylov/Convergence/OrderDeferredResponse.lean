import krylov.Convergence.OrderDeferredAffine
import krylov.Functions.RFCCanonicalQuadratic
import krylov.Cancellation.DeferredDataResidualResponse
import krylov.Methods.CorrectionFreeSearch

/-!
Article: main_krylov, thm:D and thm:DC, full physical deferred derivative.
Use: identify the actual deferred output derivative for arbitrary symmetric
physical segment perturbations, including a drifting first secant, with
the printed canonical consecutive-increment response.
Source: actual affine residual differentiation, true CG frame exhaustion
and exact inverse-root reconstruction of physical tensor differences.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Finset krylov.Cancellation krylov.Methods krylov.Reference
  krylov.Functions krylov.Stability krylov.Variation krylov.Envelope krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Genuine consecutive canonical slices reconstruct the original physical
sequence modulo its common initial drift. Article: thm:D, DC. -/
theorem deferred_cumulative_physical (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : ℕ → E →L[ℝ] E) (i : ℕ) :
    cumulativeDrift base (fun l=>physicalCanonicalMatrix base hb (W (l+1)-W l)) i=W i-W 0 := by
  have hh:=canonical_path_of_physical_differences base hb W i
  simp only [canonicalFCPath,one_smul] at hh
  exact add_left_cancel hh

/-- The original deferred response has exactly the physical affine residual
coordinates, even with nonzero common first-secant drift. Article: thm:D. -/
theorem deferred_response_physical_slices
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (W : ℕ → E →L[ℝ] E) (epsilon : ℝ) (i : ℕ) (hi : i<k) :
    inner ℝ (canonicalCGStep base g i)
      (deferredResponse base g k epsilon (fun l=>physicalCanonicalMatrix base hb (W (l+1)-W l)))=
      epsilon*(∑ j∈Ico (i+1) k,inner ℝ (referenceStep (cgOperator base) g i)
        ((W j-W i) (referenceStep (cgOperator base) g j)))+
      inner ℝ (referenceStep (cgOperator base) g i) ((W k-W i) (referenceStep (cgOperator base) g k)) := by
  let C:=fun l=>physicalCanonicalMatrix base hb (W (l+1)-W l)
  have hdiff j a : cumulativeDrift base C j-cumulativeDrift base C a=W j-W a := by
    rw [deferred_cumulative_physical,deferred_cumulative_physical]
    abel
  simpa only [hdiff] using deferred_response_physical_coordinates base hb g k hcount epsilon C i hi

/-- The actual full deferred terminal-gradient derivative for arbitrary
symmetric affine physical operators is exactly the printed response on
true consecutive canonical increments. No common drift is suppressed.
Article: main_krylov, thm:D and thm:DC. -/
theorem deferred_affine_full_hasDerivAt
    (estimate : History E → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (W : ℕ → E →L[ℝ] E) (hW : ∀ l,(W l).toLinearMap.IsSymmetric)
    (k : ℕ) (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H:=methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _=>cgOperator base) (fun _=>cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _=>cgOperator base) (fun _=>cgOperator base) g k)) :
    let Q:=cgOperator base
    let a0:=estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _=>Q) (fun _=>Q) g k)
    let m:=deferredDataMethod fullMemory (k+1) estimate
    let A:=fun (t : ℝ) j=>Q+t • W j
    HasDerivAt (fun t=>cgOperator (metricRoot base)⁻¹ (probedGradient m (A t) (A t) g (k+1)))
      (deferredResponse base g k (1-CG.length Q g k/a0)
        (fun l=>physicalCanonicalMatrix base hb (W (l+1)-W l))) 0 := by
  let Q:=cgOperator base
  let m:=deferredDataMethod fullMemory (k+1) estimate
  let A:=fun (t : ℝ) j=>Q+t • W j
  let G:=fun t=>probedGradient m (A t) (A t) g (k+1)
  let a0:=estimate (methodRun m (fun _=>Q) (fun _=>Q) g k)
  let R:=cgOperator (metricRoot base)⁻¹
  let F:=deferredResponse base g k (1-CG.length Q g k/a0)
    (fun l=>physicalCanonicalMatrix base hb (W (l+1)-W l))
  have hp:=cgOperator_positive base hb
  have hpre j (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (by omega)
  have hA j : ContDiffAt ℝ 2 (fun t=>A t j) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hA0 : A 0=fun _=>Q := by funext j;change Q+(0:ℝ) • W j=Q;module
  have hc : CGConsistent m := deferred_data_consistent fullMemory (fun _ hj=>hj) (k+1) estimate
  have hs:=deferred_data_smoothCycleAt fullMemory (fun _ hj=>hj) (k+1) estimate Q hp.1 hp.2 g (k+1) hpre 2
    (by
      intro j _ hj
      have he : j=k := by omega
      subst j
      exact ha)
    (by
      intro j _ hj
      have he : j=k := by omega
      subst j
      exact ha0)
  have hG : ContDiffAt ℝ 2 G 0 := smoothProbed_gradient_regular m hc A A (fun _=>g) 0 (k+1)
    (fun j _=>hA j) (fun j _=>hA j) contDiffAt_const Q hA0 hA0 hp.1 hp.2 hpre hs
  have hG0 : G 0=0 := by
    dsimp only [G]
    rw [hA0,probedGradient,quadratic_gradient_eq_cg m hc Q hp.1 hp.2]
    exact (cg_stopping_iff base hb g (k+1)).mpr (by omega)
  have hS0 j : probedStep m (A 0) (A 0) g j=referenceStep Q g j := by
    rw [hA0]
    exact quadratic_probedStep_eq_cg m hc Q hp.1 hp.2 g j
  have hder : R (deriv G 0)=F := by
    apply canonical_step_inner_ext base hb g hcount
    intro i hi
    have hSi:=(smoothProbed_fields_regular m hc A A (fun _=>g) 0 (k+1)
      (fun j _=>hA j) (fun j _=>hA j) contDiffAt_const Q hA0 hA0 hp.1 hp.2 hpre hs i (by omega)).2.2.1
    have hiD:=((hSi.differentiableAt (by norm_num)).hasDerivAt.inner ℝ
      (hG.differentiableAt (by norm_num)).hasDerivAt).deriv
    simp only [hG0,inner_zero_right,add_zero,hS0] at hiD
    have hpair : inner ℝ (referenceStep Q g i) (deriv G 0)=inner ℝ (canonicalCGStep base g i) (R (deriv G 0)) :=
      canonical_search_pairing base hb _ _
    rw [←hpair,←hiD]
    by_cases hik : i=k
    · subst i
      have heq : (fun t=>inner ℝ (probedStep m (A t) (A t) g k) (G t))=fun _ : ℝ=>(0:ℝ) :=
        funext (fun t=>correctionFree_last_residual m (fun _ _=>rfl) (A t) (A t) g k)
      rw [heq,deriv_const]
      exact (deferred_response_last_coordinate base hb g k (by omega) _ _).symm
    · have hik' : i<k := by omega
      rw [deferred_affine_residual_derivative estimate base hb g W hW A k
        (fun j _=>hA j) hA0 (by omega) ha ha0 i hik']
      exact (deferred_response_physical_slices base hb g k (by omega) W _ i hik').symm
  have hd:=R.hasFDerivAt.comp_hasDerivAt 0 (hG.differentiableAt (by norm_num)).hasDerivAt
  rwa [hder] at hd

end
end krylov.Convergence
