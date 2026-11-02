import krylov.Correction.GatedFullContraction
import krylov.Correction.GatedPhaseGrowth
import krylov.Correction.GatedCanonical

/-!
Article: main_krylov, thm:UCg, genuine full terminal correction contraction.
Use: Read real correction acceptance from the executed query trace and
contract the actual full-model output directly from its measured spectral gate.
Source: original finite gated executor, true full observed Gram/inverse bounds,
exact canonical gate covariance and genuine exact-search gradient growth.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine gated phase performs a correction query exactly when both of its actual observed tests pass on a nonempty old window.
Use: Finish the small-intermediate-line case of the genuine uniform gated-RFC bound.
Article: main_krylov, thm:UCg, actual full terminal contraction.
Proof: Execute the real finite correction tree in each actual spectral/defect branch. The accepted one-query trace is nonempty, including a zero correction displacement; both real fallback traces are empty.
-/
theorem gatedArrayPhase_trace_nonempty_iff {p : ℕ} (γ : ℝ) (s y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) :
    (gatedArrayPhase γ s y g d z B).trace≠[] ↔
      matrixSpectralGate γ (pairModel (Fin.cons d s) (Fin.cons z y)) ∧ 0<p ∧ ‖pairDefect s y‖<1 := by
  classical
  unfold gatedArrayPhase
  split
  · rename_i hgate
    unfold rfcArrayPhase
    split
    · rename_i hdef
      constructor
      · intro _; exact ⟨hgate,hdef⟩
      · intro _ hn; cases hn
    · rename_i hdef
      constructor
      · intro hn; exact (hn rfl).elim
      · intro h; exact (hdef h.2).elim
  · rename_i hgate
    constructor
    · intro hn; exact (hn rfl).elim
    · intro h; exact (hgate h.1).elim

/-- Every actually queried full final gated model contracts the true returned gradient by its real operator-and-pair error, with a dimension-and-threshold-only constant.
Use: Finish the small-intermediate-line case of the genuine uniform gated-RFC bound.
Article: main_krylov, thm:UCg, actual full terminal contraction.
Proof: Read both accepted original gates from the real query trace. Their true energies and normalized spectrum justify the full Gram and model inverses. Apply the proved actual full correction contraction and the real post-search gradient bound; the full-dimension identity is required but no basis or conditioning conclusion is assumed.
-/
theorem gatedArrayPhase_full_correction_contraction {p n : ℕ}
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (g d : EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hdim : p+1=n)
    {γ ε η : ℝ} (hγ : 0<γ) (hε : 0≤ε) (hη : 0≤η) (hεη : ε≤η) (hhalf : η≤1/2)
    (hsmall : (n : ℝ)*η≤γ/4)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hA : ‖A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (htrace : (gatedArrayPhase γ s y g d (A d) B).trace≠[]) :
    ‖(gatedArrayPhase γ s y g d (A d) B).gradient‖≤
      (5*((Real.sqrt (γ/4))⁻¹*(n : ℝ)*(γ/2)⁻¹*Real.sqrt n))*(ε+η)*‖g‖ := by
  subst n
  obtain ⟨hgate,hp,hdefect⟩ := (gatedArrayPhase_trace_nonempty_iff γ s y g d (A d) B).mp htrace
  obtain ⟨he,hherm,heigen⟩ := hgate
  have henergy (i : Fin (p+1)) : 0 < inner ℝ ((Fin.cons d s : Fin (p+1) → _) i)
      ((Fin.cons (A d) y : Fin (p+1) → _) i) := by
    simpa only [pairModel,max_self,min_self] using he i
  have heigen' : ∀ i, γ≤(observedPairModel_hermitian (Fin.cons d s) (Fin.cons (A d) y)).eigenvalues i := by
    simpa only [diagonalNormalizedModel,observedPairModel,pairModel,max_self,min_self] using heigen
  have hyU (i : Fin (p+1)) : ‖(Fin.cons (A d) y : Fin (p+1) → _) i-
      (Fin.cons d s : Fin (p+1) → _) i‖≤η*‖(Fin.cons d s : Fin (p+1) → _) i‖ := by
    refine Fin.cases ?_ (fun i => hy i) i
    have ht := ((A-ContinuousLinearMap.id ℝ _).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (hA.trans hεη) (norm_nonneg d))
    simpa only [Fin.cons_zero,_root_.sub_apply,ContinuousLinearMap.id_apply] using ht
  have hout := full_observed_gate_correction_contraction (Fin.cons d s) (Fin.cons (A d) y)
    (searchedGradient g d (A d)) B henergy hγ hε hη hhalf hsmall hyU heigen' hB
  have hpost := actual_searched_gradient_norm A g d hA (hεη.trans hhalf)
  have hprod := mul_le_mul_of_nonneg_left hpost
    (by positivity : 0≤((Real.sqrt (γ/4))⁻¹*((p+1 : ℕ) : ℝ)*(γ/2)⁻¹*Real.sqrt (p+1))*(ε+η))
  unfold gatedArrayPhase
  rw [ite_eq_left ⟨he,hherm,heigen⟩,rfcArrayPhase,ite_eq_left ⟨hp,hdefect⟩]
  norm_num only [Nat.cast_add,Nat.cast_one] at hout hprod ⊢
  exact (hout.trans hprod).trans_eq (by ring)

/-- The real presence of a gated correction query is unchanged by the genuine positive-root primal/dual coordinates.
Use: Finish the small-intermediate-line case of the genuine uniform gated-RFC bound.
Article: main_krylov, thm:UCg, actual full terminal contraction.
Proof: The true augmented pair model and old observed defect are exactly preserved, so the actual two accepted tests and genuine nonempty-query condition agree.
-/
theorem gatedArrayPhase_canonical_trace_nonempty {n p : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (γ : ℝ)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (g d z : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
    (gatedArrayPhase γ (primalWindow base s) (dualWindow base y) (J g) (R d) (J z)
      (canonicalOperator base B)).trace≠[] ↔ (gatedArrayPhase γ s y g d z B).trace≠[] := by
  dsimp only
  rw [gatedArrayPhase_trace_nonempty_iff,gatedArrayPhase_trace_nonempty_iff]
  have hU : Fin.cons (Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base) d) (primalWindow base s)=
      primalWindow base (Fin.cons d s) := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hZ : Fin.cons (Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹ z) (dualWindow base y)=
      dualWindow base (Fin.cons z y) := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [hU,hZ,canonical_pairModel base hb,canonical_pairDefect base hb]

end
end krylov.Correction
