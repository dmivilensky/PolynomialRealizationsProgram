import krylov.Nonlinear.RFCSGrowth
import krylov.Nonlinear.RFCSLocality
import krylov.Nonlinear.GradientLocal

/-!
Article: main_krylov, thm:RFCS, genuine uniform finite-probe localization.
Use: Prove that every actual nonlinear RFC-S iterate and finite probe stays
in the original local gradient domain uniformly before compact full-active
references and bounded probe lengths, without assuming trajectory bounds.
Source: coordinatewise McShane extension with the proved Euclidean dimension
factor, actual measured secant representatives, genuine compact prefix growth
and exact locality of the complete nonlinear gradient-query executor.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference
open scoped NNReal
variable {k : ℕ}

/-- Small genuine local gradient-model Lipschitz error yields one uniform cycle radius on which every original nonlinear RFC-S iterate and bounded finite probe is localized, with actual gradient and direction bounds proportional to the initial cycle scale.
Use: Justify substitution of the real local averaged Hessians in the genuine operator-source remainder theorem.
Article: main_krylov, thm:RFCS, complete genuine nonlinear query localization.
Proof: Extend the actual local gradient error globally. Its real nonlinear run has the proved uniform operator-prefix growth. Sum its true total steps and bound the finite probe displacements, choosing the initial scale before all bounded probes. All actual auxiliary requests therefore lie in the original ball. Oracle locality identifies each entire finite history with the original function run and transfers the derived bounds.
-/
theorem compact_rfcs_nonlinear_localization (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧
      ∀ G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)), G 0=0 →
      ∀ r B T : ℝ, 0<r → 0<B → 0≤T →
      ∀ η : ℝ≥0, LipschitzOnWith η (fun x => G x-cgOperator base x) (ball 0 r) →
      2*((NNReal.sqrt (k+1 : ℕ)*η : ℝ≥0) : ℝ)≤δ →
      ((NNReal.sqrt (k+1 : ℕ)*η : ℝ≥0) : ℝ)*B≤δ →
      ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) →
      (∀ i≤k+1, rfcSFunctionPoint fullMemory G (ε • u) h i∈ball 0 r ∧
        ‖(rfcSFunctionRun fullMemory G (ε • u) h i).gradient‖≤ε*M ∧
        ‖rfcSFunctionPoint fullMemory G (ε • u) h i‖≤ε*(B+(k+1 : ℕ)*M)) ∧
      (∀ i<k+1, rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
        windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
          (rfcSFunctionRun fullMemory G (ε • u) h i).gradient∈ball 0 r ∧
        ‖windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
          (rfcSFunctionRun fullMemory G (ε • u) h i).gradient‖≤ε*M ∧
        ‖rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
          windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
            (rfcSFunctionRun fullMemory G (ε • u) h i).gradient‖≤ε*(B+((k+1 : ℕ)+T)*M)) := by
  obtain ⟨δ,M,hδ,hM,hgrowth⟩ := compact_rfcs_function_prefix_bounds base hb K hK hN
  refine ⟨δ,M,hδ,hM,?_⟩
  intro G h₀ r B T hr hB hT η hlocal hη hηB
  -- The auxiliary oracle supplies global control before any original-query localization is known.
  obtain ⟨F,hagree,hF⟩ := exists_gradient_model_extension G (cgOperator base) hlocal
  have hF₀ : F 0=0 := (hagree (mem_ball_self hr)).symm.trans h₀
  let D := B+((k+1 : ℕ)+T)*M
  have hD : 0≤D := by dsimp only [D]; positivity
  have hD' : 0<D+1 := by linarith
  refine ⟨r/(D+1),div_pos hr hD',?_⟩
  intro ε hε he u hu hKu h hh hTbound
  have her : ε*D<r := by
    have he' := (lt_div_iff₀ hD').mp he
    nlinarith
  have hinit : ‖ε⁻¹ • F (ε • u)-cgOperator base u‖≤δ :=
    (normalized_gradient_error_le F (cgOperator base) hF₀ hF u hε).trans
      ((mul_le_mul_of_nonneg_left hu (NNReal.coe_nonneg _)).trans hηB)
  have hgrowthF := hgrowth F (ε • u) h hh _ hF hη ε hε (cgOperator base u) hKu hinit
  have hpoint i (hi : i≤k+1) : ‖rfcSFunctionPoint fullMemory F (ε • u) h i‖≤ε*(B+(k+1 : ℕ)*M) := by
    calc
      _ ≤ ‖rfcSFunctionPoint fullMemory F (ε • u) h i-ε • u‖+‖ε • u‖ := by
        simpa only [sub_add_cancel] using norm_add_le (rfcSFunctionPoint fullMemory F (ε • u) h i-ε • u) (ε • u)
      _ ≤ (k+1 : ℕ)*(ε*M)+ε*B := add_le_add (hgrowthF.1 i hi).2 (by
        rw [norm_smul,Real.norm_of_nonneg hε.le]
        exact mul_le_mul_of_nonneg_left hu hε.le)
      _ = _ := by ring
  have hpointBall i (hi : i≤k+1) : rfcSFunctionPoint fullMemory F (ε • u) h i∈ball 0 r := by
    rw [mem_ball_zero_iff]
    apply lt_of_le_of_lt (hpoint i hi) _
    apply lt_of_le_of_lt _ her
    apply mul_le_mul_of_nonneg_left _ hε.le
    dsimp only [D]
    nlinarith
  have hprobeBound i (hi : i<k+1) : ‖rfcSFunctionPoint fullMemory F (ε • u) h i+h i •
      windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory F (ε • u) h i))
        (rfcSFunctionRun fullMemory F (ε • u) h i).gradient‖≤ε*D := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    have hdir := hgrowthF.2 i hi
    have hp := hpoint i hi.le
    have hs := mul_le_mul (hTbound i hi) hdir (norm_nonneg _) hT
    dsimp only [D]
    nlinarith
  have hprobe i (hi : i<k+1) : rfcSFunctionPoint fullMemory F (ε • u) h i+h i •
      windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory F (ε • u) h i))
        (rfcSFunctionRun fullMemory F (ε • u) h i).gradient∈ball 0 r := by
    rw [mem_ball_zero_iff]
    exact (hprobeBound i hi).trans_lt her
  -- Agreement is needed only at the genuine auxiliary requests, already proved local above.
  have heq i (hi : i≤k+1) : rfcSFunctionRun fullMemory F (ε • u) h i=rfcSFunctionRun fullMemory G (ε • u) h i := by
    apply rfcSFunctionRun_congr
    · exact (hagree (by simpa only [rfcSFunctionPoint,rfcSFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero] using hpointBall 0 (by omega))).symm
    · intro j hj
      exact (hagree (hprobe j (hj.trans_le hi))).symm
    · intro j hj
      exact (hagree (hpointBall (j+1) (by omega))).symm
  refine ⟨?_,?_⟩
  · intro i hi
    have hp := hpointBall i hi
    have hg := (hgrowthF.1 i hi).1
    simp only [rfcSFunctionPoint,heq i hi] at hp
    rw [heq i hi] at hg
    have hn := hpoint i hi
    simp only [rfcSFunctionPoint,heq i hi] at hn
    exact ⟨hp,hg,hn⟩
  · intro i hi
    have hp := hprobe i hi
    have hd := hgrowthF.2 i hi
    simp only [rfcSFunctionPoint,heq i hi.le] at hp
    rw [heq i hi.le] at hd
    have hn := hprobeBound i hi
    simp only [rfcSFunctionPoint,heq i hi.le] at hn
    exact ⟨hp,hd,hn⟩

end
end krylov.Nonlinear
