import krylov.Correction.GatedUniformCutoff
import krylov.Correction.GatedSmallLine
import krylov.Correction.GatedTerminalContraction

/-!
Article: main_krylov, thm:UCg, exact domains and performed-query homogeneity.
Use: Remove initial-gradient normalization while preserving genuine observed
inverse/search domains and the actual last correction-query condition.
Source: original true gated-RFC field homogeneity, real finite observed
coordinates, determinant scaling and exact measured-gate scale covariance.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full observed-list conjugacy determinant has exactly its genuine finite retained-age coordinate determinant.
Use: Remove actual initial-gradient normalization in the original uniform gated-RFC theorem.
Article: main_krylov, thm:UCg, genuine domain and query homogeneity.
Proof: Use the actual executed step/secant transcript and the true retained coordinates; their common finite index equivalence preserves the original determinant.
-/
theorem full_probed_conjugacy_det (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) :
    (crossGram (windowImages (selectedWindow fullMemory (methodRun m A B g i)))
      (windowSteps (selectedWindow fullMemory (methodRun m A B g i)))).det=
      (crossGram (fun j : Fin (min (fullMemory i) i) => probedSecant m A B g (i-1-j.val))
        (fun j : Fin (min (fullMemory i) i) => probedStep m A B g (i-1-j.val))).det := by
  rw [selectedWindow_methodRun]
  have hc := retainedWindow_coordinates (probedStep m A B g) (probedSecant m A B g) i (fullMemory i)
  have ht := crossGram_det_of_coordinates _ _ _ _ hc.1 hc.2
  exact ht

variable {n : ℕ}

/-- Every nonzero common initial-gradient scaling preserves the genuine finite full gated-run inverse and search domains.
Use: Remove actual initial-gradient normalization in the original uniform gated-RFC theorem.
Article: main_krylov, thm:UCg, genuine domain and query homogeneity.
Proof: Exact actual field homogeneity scales both real observed step and secant arrays by the same nonzero scalar. Their true conjugacy determinant acquires a nonzero even-degree factor, and the genuine current curvature acquires its nonzero square.
-/
theorem gatedFullRunDefined_scalar (γ : ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) (N : ℕ)
    (hdefined : gatedFullRunDefined γ A B g N) : gatedFullRunDefined γ A B (c • g) N := by
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  unfold gatedFullRunDefined
  dsimp only
  intro i hi
  have hS : (fun j : Fin (min (fullMemory i) i) => probedStep m A B (c • g) (i-1-j.val))=
      (fun j => c • probedStep m A B g (i-1-j.val)) := by
    funext j
    have hj := j.isLt
    have hm := Nat.min_le_right (fullMemory i) i
    exact ((gated_scalar fullMemory γ A B g c hc i).2 _ (by omega)).2.1
  have hY : (fun j : Fin (min (fullMemory i) i) => probedSecant m A B (c • g) (i-1-j.val))=
      (fun j => c • probedSecant m A B g (i-1-j.val)) := by
    funext j
    have hj := j.isLt
    have hm := Nat.min_le_right (fullMemory i) i
    exact ((gated_scalar fullMemory γ A B g c hc i).2 _ (by omega)).2.2
  have hd := ((gated_scalar fullMemory γ A B g c hc (i+1)).2 i (Nat.lt_succ_self i)).1
  refine ⟨?_,?_⟩
  · have hunit := (hdefined i hi).1
    rw [full_probed_conjugacy_det] at hunit ⊢
    rw [hS,hY,crossGram_scalar,Matrix.det_smul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hc)) (isUnit_iff_ne_zero.mp hunit))
  · rw [hd,map_smul,real_inner_smul_left,real_inner_smul_right]
    exact mul_ne_zero hc (mul_ne_zero hc (hdefined i hi).2)

/-- Every genuine positive-horizon defined full gated run has a strictly positive actual initial metric-gradient norm.
Use: Remove actual initial-gradient normalization in the original uniform gated-RFC theorem.
Article: main_krylov, thm:UCg, genuine domain and query homogeneity.
Proof: The actual metric root identities rule out a nonzero initial vector with zero dual image. Zero initial data would make the real first direction and curvature zero, contradicting the original defined-search domain.
-/
theorem gated_defined_initial_metric_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (γ : ℝ) (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 1≤N)
    (hdefined : gatedFullRunDefined γ A B g N) :
    0<‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  apply norm_pos_iff.mpr
  intro hj
  have hr : R g=0 := by
    rw [← canonical_base_dual base hb g,hj,map_zero]
  have hg : g=0 := by
    have ht := canonical_primal_dual_cancel base hb g
    change J (R g)=g at ht
    rw [hr,map_zero] at ht
    exact ht.symm
  have hcurv := (hdefined 0 (by omega)).2
  have hd : m.direction (methodRun m A B g 0)=0 := by
    change windowDirection [] g=0
    rw [hg,windowDirection_zero]
  change inner ℝ (m.direction (methodRun m A B g 0)) (A 0 (m.direction (methodRun m A B g 0)))≠0 at hcurv
  rw [hd,map_zero,inner_zero_left] at hcurv
  exact hcurv rfl

/-- Every nonzero common scaling preserves whether the actual finite spectral-gated phase performs a correction query.
Use: Remove actual initial-gradient normalization in the original uniform gated-RFC theorem.
Article: main_krylov, thm:UCg, genuine domain and query homogeneity.
Proof: The true augmented measured spectral test and old observed defect are exactly scale invariant, while the real retained coefficient dimension stays unchanged.
-/
theorem gatedArrayPhase_scalar_trace_nonempty {p : ℕ} (γ : ℝ) (s y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (c : ℝ) (hc : c≠0) :
    (gatedArrayPhase γ (fun i => c • s i) (fun i => c • y i) (c • g) (c • d) (c • z) B).trace≠[] ↔
      (gatedArrayPhase γ s y g d z B).trace≠[] := by
  have hU : (Fin.cons (c • d) (fun i => c • s i) : Fin (p+1) → E)=fun i => c • (Fin.cons d s : Fin (p+1) → E) i := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hZ : (Fin.cons (c • z) (fun i => c • y i) : Fin (p+1) → E)=fun i => c • (Fin.cons z y : Fin (p+1) → E) i := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [gatedArrayPhase_trace_nonempty_iff,gatedArrayPhase_trace_nonempty_iff,hU,hZ,
    pairSpectralGate_scalar γ (Fin.cons d s) (Fin.cons z y) c hc,pairDefect_scalar s y c hc]

/-- Every nonzero common initial-gradient scaling preserves the real correction-query presence at each actual gated iteration.
Use: Remove actual initial-gradient normalization in the original uniform gated-RFC theorem.
Article: main_krylov, thm:UCg, genuine domain and query homogeneity.
Proof: The genuine full field homogeneity identifies every actual old step, secant, current gradient, direction and probe. Their true finite-array phase has the proved exact performed-query scale invariance through both fallback branches.
-/
theorem gated_scalar_trace_nonempty (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (i : ℕ) :
    let m := gatedMethod memory γ (E := E)
    (probedPhase m A B (c • g) i).trace≠[] ↔ (probedPhase m A B g i).trace≠[] := by
  let m := gatedMethod memory γ (E := E)
  have hs : (fun j : Fin (min (memory i) i) => probedStep m A B (c • g) (i-1-j.val))=
      fun j => c • probedStep m A B g (i-1-j.val) := by
    funext j
    have hj := j.isLt
    have hm := Nat.min_le_right (memory i) i
    exact ((gated_scalar memory γ A B g c hc i).2 _ (by omega)).2.1
  have hy : (fun j : Fin (min (memory i) i) => probedSecant m A B (c • g) (i-1-j.val))=
      fun j => c • probedSecant m A B g (i-1-j.val) := by
    funext j
    have hj := j.isLt
    have hm := Nat.min_le_right (memory i) i
    exact ((gated_scalar memory γ A B g c hc i).2 _ (by omega)).2.2
  have hg := (gated_scalar memory γ A B g c hc i).1
  have hd := ((gated_scalar memory γ A B g c hc (i+1)).2 i (Nat.lt_succ_self i)).1
  dsimp only
  rw [probedGated_phase_array,probedGated_phase_array]
  change (gatedArrayPhase γ _ _ (probedGradient m A B (c • g) i) _ _ _).trace≠[] ↔
    (gatedArrayPhase γ _ _ (probedGradient m A B g i) _ _ _).trace≠[]
  rw [hs,hy,hg,hd,map_smul]
  exact gatedArrayPhase_scalar_trace_nonempty γ _ _ _ _ _ (B i) c hc

end
end krylov.Correction
