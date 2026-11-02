import krylov.Realization.BudgetConversion
import krylov.Stability.AnalyticFC
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: main_krylov, prop:conv, actual adaptive FC quadratic budget-conversion remainder.
Use: discharge the trajectory replacement order for the real executed FC
steps from proved actual analytic regularity, rather than assume step closeness.
Source: exact cumulative injection, true quadratic transcript and analytic first-order displacement bounds.
-/

namespace krylov.Realization
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators InnerProductSpace
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual canonical line step executed by the full-memory adaptive FC policy.
Use: compare genuine observed FC displacements with their true canonical CG reference steps.
Article: main_krylov, prop:conv, actual A^(1/2)s_k. -/
def canonicalFCStep (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g k)

/-- The actually executed canonical FC steps have genuine first-order reference errors near every active positive quadratic prefix.
Use: supplies the true trajectory estimate needed by the quadratic budget conversion, with all actual solve domains discharged.
Article: main_krylov, prop:conv and lem:U, actual step replacement.
Proof: real adaptive FC steps are analytic by the proved executed solve
induction; their true quadratic values are the true CG steps. Differentiability bounds the actual step difference by the perturbation norm. -/
theorem canonicalFCStep_reference_order (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun p => A p k) 0) (hA0 : A 0=fun _ => cgOperator base)
    (N : ℕ) (hpre : ∀ k<N, CG.gradient (cgOperator base) g k≠0) {k : ℕ} (hk : k<N) :
    (fun p => canonicalFCStep base (A p) g k-canonicalCGStep base g k)=O[𝓝 (0 : X)] (fun p => ‖p‖) := by
  -- The estimate concerns the actual data-only FC coefficient solve and its genuine physical step.
  have ht := (quadraticFC_prefix_analytic A (fun _ => g) 0 hA analyticAt_const (cgOperator base) hA0
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 N hpre).2 k hk
  have hs : AnalyticAt ℝ (fun p => canonicalFCStep base (A p) g k) 0 :=
    analytic_operator_apply analyticAt_const ht.2
  have href : canonicalFCStep base (A 0) g k=canonicalCGStep base g k := by
    unfold canonicalFCStep
    rw [hA0,(fullFC_reference_step (cgOperator base) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g k).2.2]
    rfl
  simpa only [href,sub_zero] using hs.differentiableAt.isBigO_sub.norm_right

/-- Replacing the true adaptive FC steps by true CG steps in the actual cumulative secant injection has a proved quadratic remainder.
Use: the source budget conversion is now applied to a real adaptive algorithm with its step regularity discharged.
Article: main_krylov, prop:conv, ι̂_j=Σ_lE_l(e_j⁰−e_(l+1)⁰)+O(ω²).
Proof: actual FC analytic regularity makes each true canonical step error
first order. Each is multiplied by a first-order primitive canonical increment; the exact cumulative finite injection sums therefore have quadratic difference. -/
theorem fc_secantInjection_quadratic (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun p => A p k) 0) (hA0 : A 0=fun _ => cgOperator base)
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (j : ℕ) (hpre : ∀ k<j, CG.gradient (cgOperator base) g k≠0)
    (hD : ∀ l<j, (fun p => D p l)=O[𝓝 (0 : X)] (fun p => ‖p‖)) :
    (fun p => secantInjection (D p) (canonicalFCStep base (A p) g) j-
      ∑ l∈range j, D p l (cgCanonicalError base g j-cgCanonicalError base g (l+1)))=O[𝓝 (0 : X)]
        (fun p => ‖p‖^2) := by
  -- Exact finite telescoping provides the reference term; only actual step errors need estimation.
  have hterm (k : ℕ) (hk : k∈range j) (l : ℕ) (hl : l∈range k) :
      (fun p => D p l (canonicalFCStep base (A p) g k-canonicalCGStep base g k))=O[𝓝 (0 : X)] (fun p => ‖p‖^2) := by
    have hs := canonicalFCStep_reference_order base hb g A hA hA0 j hpre (mem_range.mp hk)
    have hh := krylov.LinearAlgebra.operator_action_order (fun p => D p l)
      (fun p => canonicalFCStep base (A p) g k-canonicalCGStep base g k)
      (fun p => ‖p‖) (fun p => ‖p‖) (hD l (by have := mem_range.mp hl; have := mem_range.mp hk; omega)) hs
    simpa only [pow_two] using hh
  have hsum := Asymptotics.IsBigO.sum (fun k hk => Asymptotics.IsBigO.sum (fun l hl => hterm k hk l hl))
  apply hsum.congr_left
  intro p
  rw [← cg_secantInjection base hb g (D p) j]
  simp only [secantInjection,← sum_sub_distrib,← map_sub,Finset.sum_apply]

end
end krylov.Realization
