import krylov.Design.FCDesignBridge
import krylov.Variation.FrobeniusResponse

/-!
Article: Proposition B.9 [prop:HS] of krylov.tex.
Use: identify the sharp joint Hilbert--Schmidt coefficient of actual CG
references with the square root of the genuine gamma-one design optimum.
Source: the proved symmetric cross-block Frobenius extremum, the actual
CG/Christoffel dictionary and the prescribed-atom design theorem.
-/

namespace krylov.Cost
noncomputable section
open Matrix Set MeasureTheory jacobi.Finite krylov.Reference krylov.Stability
  krylov.Design krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The actual initial-error-normalized sharp joint Frobenius coefficient.
The sum contains precisely the preterminal reference errors. -/
def hsCoefficient {M : ℕ} {μ κ : ℝ} (R : FCReference (M + 1) μ κ) : ℝ :=
  Real.sqrt (∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2) /
    Real.sqrt 2 / R.initialNorm

/-- The genuine Hilbert--Schmidt coefficient is nonnegative. -/
theorem hsCoefficient_nonneg {M : ℕ} {μ κ : ℝ} (R : FCReference (M + 1) μ κ) :
    0 ≤ hsCoefficient R := by
  exact div_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) R.initialNorm_pos.le

/-- Every actual symmetric increment family with the source joint squared
Frobenius budget obeys this true initial-normalized coefficient. -/
theorem actual_hs_response_le {M : ℕ} {μ κ : ℝ} (R : FCReference (M + 1) μ κ)
    (E : ℕ → Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (hE : ∀ l ∈ Finset.range M, (E l).IsSymm) {ω : ℝ} (hω : 0 ≤ ω)
    (hbudget : ∑ l ∈ Finset.range M, chebyshev1.hsSq (E l) ≤ ω ^ 2) :
    ‖fullCycleResponse R.base R.gradient (Finset.range M) E‖ / R.initialNorm ≤ ω * hsCoefficient R := by
  have h := frobenius_response_le R.base R.positive R.gradient (Finset.range M)
    (fun l hl ↦ by have := R.full; have := Finset.mem_range.mp hl; omega) E hE ω hω hbudget
  have hp : (∑ l ∈ Finset.range M, ‖cgCanonicalError R.base R.gradient (l + 1)‖ ^ 2) =
      ∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun l ↦ ‖cgCanonicalError R.base R.gradient (l + 1)‖ ^ 2) M).symm
  rw [hp] at h
  apply (div_le_iff₀ R.initialNorm_pos).mpr
  have hd := (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    (show ‖fullCycleResponse R.base R.gradient (Finset.range M) E‖ * Real.sqrt 2 ≤
      ω * Real.sqrt (∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2) by
      nlinarith)
  apply hd.trans_eq
  unfold hsCoefficient
  field_simp [R.initialNorm_pos.ne']

/-- A genuine symmetric increment family attains the stated normalized
response under the actual joint budget. Nonempty criteria spend the full
budget; the empty criterion has its genuine zero attaining family. -/
theorem actual_hs_response_attained {M : ℕ} {μ κ : ℝ} (R : FCReference (M + 1) μ κ)
    {ω : ℝ} (hω : 0 ≤ ω) :
    ∃ E : ℕ → Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ,
      (∀ l ∈ Finset.range M, (E l).IsSymm) ∧
      (∑ l ∈ Finset.range M, chebyshev1.hsSq (E l)) ≤ ω ^ 2 ∧
      ‖fullCycleResponse R.base R.gradient (Finset.range M) E‖ / R.initialNorm = ω * hsCoefficient R := by
  by_cases hM : M = 0
  · subst M
    refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
    · simp
    · simpa using sq_nonneg ω
    · simp [fullCycleResponse, hsCoefficient]
  · obtain ⟨E, hE, hbudget, hvalue⟩ := frobenius_response_attained R.base R.positive R.gradient
      (by have := R.full; omega) (Finset.range M) (Finset.nonempty_range_iff.mpr hM)
      (fun l hl ↦ by have := R.full; have := Finset.mem_range.mp hl; omega) ω hω
    refine ⟨E, hE, hbudget.le, ?_⟩
    rw [hvalue]
    have hp : (∑ l ∈ Finset.range M, ‖cgCanonicalError R.base R.gradient (l + 1)‖ ^ 2) =
        ∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2 :=
      (Fin.sum_univ_eq_sum_range (fun l ↦ ‖cgCanonicalError R.base R.gradient (l + 1)‖ ^ 2) M).symm
    rw [hp]
    unfold hsCoefficient
    ring

/-- The true reference error-square profile is its gamma-one Christoffel
criterion times the square of the actual initial error. -/
theorem errorProfile_eq_design (I : chebyshev1.SpectralInterval) (M : ℕ)
    (R : FCReference (M + 1) I.mu I.kappa) :
    (∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2) =
      R.initialNorm ^ 2 * intervalObjective I M (fun _ ↦ 1) 1
        (atomicProbability (energySpectralData R.base R.positive R.gradient R.nonzero)
          (fun i ↦ ⟨_, fcReference_energy_nodes I R i⟩)) := by
  simp only [intervalObjective, mixedObjective, one_mul, Real.rpow_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [interval_christoffel_atomic I _ (fcReference_energy_nodes I R)
    (by have := R.full; omega : i.val + 1 < referenceAtomCount R.base R.positive R.gradient)]
  exact cg_energy_christoffel R.base R.positive R.gradient R.nonzero (by have := R.full; omega)

/-- Squaring the actual sharp Frobenius coefficient gives one half of the
actual gamma-one design objective, with no spectral realization premise. -/
theorem hsCoefficient_sq (I : chebyshev1.SpectralInterval) (M : ℕ)
    (R : FCReference (M + 1) I.mu I.kappa) :
    hsCoefficient R ^ 2 = intervalObjective I M (fun _ ↦ 1) 1
      (atomicProbability (energySpectralData R.base R.positive R.gradient R.nonzero)
        (fun i ↦ ⟨_, fcReference_energy_nodes I R i⟩)) / 2 := by
  have hprofile : 0 ≤ ∑ i : Fin M, ‖cgCanonicalError R.base R.gradient (i.val + 1)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  unfold hsCoefficient
  rw [div_pow, div_pow, Real.sq_sqrt hprofile, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    errorProfile_eq_design I M R]
  field_simp [R.initialNorm_pos.ne']

/-- Every physical reference obeys the full gamma-one design upper bound. -/
theorem hsCoefficient_le_design (I : chebyshev1.SpectralInterval) (M : ℕ)
    (R : FCReference (M + 1) I.mu I.kappa) :
    hsCoefficient R ≤ Real.sqrt (optimalValue I M (fun _ ↦ 1) 1 / 2) := by
  obtain ⟨ν, hν⟩ := intervalObjective_attains I M (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hopt := optimalValue_eq_of_maximizer I M (fun _ ↦ 1) 1 ν hν
  have hnonneg : 0 ≤ optimalValue I M (fun _ ↦ 1) 1 := by
    rw [hopt]
    exact mixedObjective_nonneg M _ (fun _ ↦ zero_le_one) _ _ _ _
  have hle := hν (atomicProbability (energySpectralData R.base R.positive R.gradient R.nonzero)
    (fun i ↦ ⟨_, fcReference_energy_nodes I R i⟩))
  rw [← hopt] at hle
  have hs := Real.sq_sqrt (div_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 2))
  have he := hsCoefficient_sq I M R
  nlinarith [hsCoefficient_nonneg R, Real.sqrt_nonneg (optimalValue I M (fun _ ↦ 1) 1 / 2)]

/-- Every genuine positive atomic design is realized by an actual physical
CG reference with precisely its gamma-one profile and unit initial error. -/
theorem atomicDesign_hs_realization (I : chebyshev1.SpectralInterval) (M : ℕ)
    (Q : AtomicIntervalDesign I (M + 1)) :
    ∃ R : FCReference (M + 1) I.mu I.kappa, R.initialNorm = 1 ∧
      hsCoefficient R ^ 2 = atomicDesignObjective I M (fun _ ↦ 1) 1 Q / 2 := by
  obtain ⟨A, hA, g, hg, hcount, hband, hinit, hprofile⟩ :=
    atomic_energy_reference_realization Q.val I.mu I.L I.mu_pos Q.property
  have hu : I.mu * I.kappa = I.L := by
    change I.mu * (I.L / I.mu) = I.L
    field_simp [I.mu_pos.ne']
  let R : FCReference (M + 1) I.mu I.kappa :=
    ⟨A, hA, g, hg, hcount, fun i ↦ by simpa only [hu] using hband i⟩
  refine ⟨R, hinit, ?_⟩
  have hp : (∑ i : Fin M, ‖cgCanonicalError A g (i.val + 1)‖ ^ 2) =
      atomicDesignObjective I M (fun _ ↦ 1) 1 Q := by
    simp only [atomicDesignObjective, intervalObjective, mixedObjective, one_mul, Real.rpow_one]
    apply Finset.sum_congr rfl
    intro i _
    rw [interval_christoffel_atomic I Q.val Q.property (by omega : i.val + 1 < M + 1)]
    simpa only [finiteChristoffelValue, ite_eq_left (by omega : i.val + 1 < M + 1)] using
      hprofile (i.val + 1)
  have hn : 0 ≤ ∑ i : Fin M, ‖cgCanonicalError A g (i.val + 1)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  change (Real.sqrt _ / Real.sqrt 2 / R.initialNorm) ^ 2 = _
  rw [show R.initialNorm = 1 from hinit, div_one, div_pow, Real.sq_sqrt hn,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hp]

/-- The actual worst Hilbert--Schmidt coefficient over full physical
references, with the harmless zero convention for an empty class. -/
def hsWorstCoefficient (I : chebyshev1.SpectralInterval) (M : ℕ) : ℝ :=
  sSup (insert 0 (range (fun R : FCReference (M + 1) I.mu I.kappa ↦ hsCoefficient R)))

/-- The exact worst physical Frobenius coefficient is the square root of
one half of the true gamma-one design optimum. Empty criteria are included. -/
theorem hsWorstCoefficient_eq_design (I : chebyshev1.SpectralInterval) (M : ℕ) :
    hsWorstCoefficient I M = Real.sqrt (optimalValue I M (fun _ ↦ 1) 1 / 2) := by
  let S := insert 0 (range (fun R : FCReference (M + 1) I.mu I.kappa ↦ hsCoefficient R))
  have hS : S.Nonempty := ⟨0, mem_insert 0 _⟩
  have hbound : ∀ x ∈ S, x ≤ Real.sqrt (optimalValue I M (fun _ ↦ 1) 1 / 2) := by
    intro x hx
    rcases hx with rfl | ⟨R, rfl⟩
    · exact Real.sqrt_nonneg _
    · exact hsCoefficient_le_design I M R
  have hb : BddAbove S := ⟨_, hbound⟩
  have hzero : 0 ≤ hsWorstCoefficient I M := le_csSup hb (mem_insert 0 _)
  apply le_antisymm
  · exact csSup_le hS hbound
  · have hval : optimalValue I M (fun _ ↦ 1) 1 ≤ 2 * hsWorstCoefficient I M ^ 2 := by
      rw [← atomicDesignValue_eq_optimalValue_all I M (M + 1) le_rfl (fun _ ↦ 1)
        (fun _ ↦ zero_le_one) (by norm_num : (0 : ℝ) < 1) le_rfl]
      let := exists_atomicIntervalDesign I (M + 1) (by omega)
      apply csSup_le (range_nonempty _)
      rintro _ ⟨Q, rfl⟩
      obtain ⟨R, _, he⟩ := atomicDesign_hs_realization I M Q
      have hr : hsCoefficient R ≤ hsWorstCoefficient I M := le_csSup hb (mem_insert_of_mem _ (mem_range_self R))
      have hs := sq_le_sq₀ (hsCoefficient_nonneg R) hzero |>.mpr hr
      nlinarith
    have hv : 0 ≤ optimalValue I M (fun _ ↦ 1) 1 := by
      obtain ⟨ν, hν⟩ := intervalObjective_attains I M (fun _ ↦ 1) (fun _ ↦ zero_le_one)
        (by norm_num : (0 : ℝ) ≤ 1)
      rw [optimalValue_eq_of_maximizer I M (fun _ ↦ 1) 1 ν hν]
      exact mixedObjective_nonneg M _ (fun _ ↦ zero_le_one) _ _ _ _
    have hs := Real.sq_sqrt (div_nonneg hv (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith [Real.sqrt_nonneg (optimalValue I M (fun _ ↦ 1) 1 / 2)]

end
end krylov.Cost
