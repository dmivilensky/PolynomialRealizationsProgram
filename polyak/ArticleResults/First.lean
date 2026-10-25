import polyak.Energy.Estimate
import polyak.Growth.Completion
import polyak.Boundary.Classification.Results
import polyak.Spectral.Compact
import polyak.CertifiedExamples.Plateaus.Results

/-!
Literal statement interfaces used by the article showcase.

Theorem 2.8 (`thm:classification`) exposes the critical coordinates.
Theorem 3.16 (`thm:modelock`) packages all continuation conclusions.
Theorem 3.17 (`thm:plateaus`) retains the whole-plateau period and support
quantifiers. Lemma A.6 (`lem:energy`) uses literal interior-data segments
in arbitrary real Hilbert spaces with the stated window width, and Lemma
A.9 (`lem:vmono`) retains the exact scaled value constant.
-/
noncomputable section
namespace polyak.ArticleResults
open Growth Duality Spectral
open scoped BigOperators

/-- Theorem 2.8 (`thm:classification`): the selected central family
has the exact three-cycle data u=1/2, x=−1/2, p=d=0 at G=1. -/
theorem classification_critical_data :
    let Z := Boundary.P5.Selection.continuation 0
    Boundary.P5.branchU 0 Z = 1/2 ∧ Boundary.P5.branchX 0 Z = -1/2 ∧
      (0:ℝ)*Z 3 = 0 ∧ (0:ℝ)*Z 4 = 0 := by
  simp only [Boundary.P5.branchU,Boundary.P5.branchX,zero_mul,add_zero,and_self]

/-- Lemma A.6 (`lem:energy`): the strict-certificate energy estimate on every
finite interpolation segment, with a window at least two beyond the lag bound. -/
private theorem completed_segment_energy {A B β t : ℝ} {M : ℕ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (hB : B ≠ 0)
    (_hM : ∀ m ∈ cert.lags, m ≤ M) :
    ∃ K : ℝ, ∃ w : ℕ, 0 < K ∧ M + 2 ≤ w ∧
      ∀ d n : ℕ, ∀ s : Segment (EuclideanSpace ℝ (Fin d)) A B β n,
      ∀ i j : ℕ, w ≤ i → i ≤ j → j + w ≤ n + 1 →
        mass (discountedEnergy s.x t) i (j + 1) ≤
          K * (energyWindow (discountedEnergy s.x t) w i +
            energyWindow (discountedEnergy s.x t) w j) := by
  obtain ⟨K,w₀,hK,henergy⟩ := cert.windowEnergyBound hB
  let w := max w₀ (M + 2)
  have hw₀ : w₀ ≤ w := le_max_left _ _
  refine ⟨K,w,hK,le_max_right _ _,?_⟩
  intro d n s i j hi hij hjn
  obtain ⟨r,hr⟩ := s.exists_run
  have hb (k : ℕ) : 0 ≤ discountedEnergy r.x t k := discountedEnergy_nonneg _ _ _
  have hmono (k : ℕ) :
      energyWindow (discountedEnergy r.x t) w₀ k ≤
        energyWindow (discountedEnergy r.x t) w k := by
    apply mass_mono hb <;> omega
  have he := (henergy d r i j (hw₀.trans hi) hij).trans
    (mul_le_mul_of_nonneg_left (add_le_add (hmono i) (hmono j)) hK.le)
  have hmass (a b : ℕ) (hbn : b ≤ n + 2) :
      mass (discountedEnergy r.x t) a b = mass (discountedEnergy s.x t) a b := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkb : k < b := (Finset.mem_Ico.mp hk).2
    simp only [discountedEnergy,hr k (by omega)]
  rw [hmass i (j+1) (by omega)] at he
  change _ ≤ K * (mass _ (i-w) (i+w+1) + mass _ (j-w) (j+w+1)) at he
  rw [hmass (i-w) (i+w+1) (by omega),hmass (j-w) (j+w+1) (by omega)] at he
  exact he


/-- Lemma A.6 (`lem:energy`), literally on the article's interior-data
segments, uniformly over all real Hilbert spaces. Completing endpoint data
and finite-span compression are proved operations and preserve every energy.
The argument n is the article's last position index; RawSegment uses n−1
transitions and hence has exactly the positions e₀,…,eₙ. -/
theorem finite_segment_energy {A B β t : ℝ} {M : ℕ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (hB : B ≠ 0)
    (hM : ∀ m ∈ cert.lags, m ≤ M) :
    ∃ K : ℝ, ∃ w : ℕ, 0 < K ∧ M + 2 ≤ w ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ n : ℕ, ∀ s : RawSegment E A B β (n-1),
      ∀ i j : ℕ, w ≤ i → i ≤ j → j + w ≤ n →
        mass (discountedEnergy s.x t) i (j + 1) ≤
          K * (energyWindow (discountedEnergy s.x t) w i +
            energyWindow (discountedEnergy s.x t) w j) := by
  obtain ⟨K,w,hK,hw,henergy⟩ := completed_segment_energy cert hB hM
  refine ⟨K,w,hK,hw,?_⟩
  intro E _ _ _ n raw i j hi hij hjn
  have hn : 1 ≤ n := by omega
  have hn' : n-1+1=n := Nat.sub_add_cancel hn
  obtain ⟨s,hs,_⟩ := raw.exists_completion
  let J := (stdOrthonormalBasis ℝ
    (Interpolation.dataSpan (fun k : Fin (n-1+2) => s.x k)
      (fun k : Fin (n-1+2) => s.σ k))).repr.toLinearIsometry
  let q := s.inSpan.map J
  have hnorm (k : ℕ) (hk : k ≤ n) : ‖q.x k‖ = ‖raw.x k‖ := by
    simp only [q,Segment.map,J.norm_map,Segment.inSpan,Interpolation.spanPosition,
      Segment.finiteIndex,←Submodule.norm_coe,hn',min_eq_left hk,hs]
  have hmass (a b : ℕ) (hbn : b ≤ n+1) :
      mass (discountedEnergy q.x t) a b = mass (discountedEnergy raw.x t) a b := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkb : k < b := (Finset.mem_Ico.mp hk).2
    simp only [discountedEnergy,hnorm k (by omega)]
  have he := henergy _ (n-1) q i j hi hij (by omega)
  rw [hmass i (j+1) (by omega)] at he
  change _ ≤ K * (mass _ (i-w) (i+w+1) + mass _ (j-w) (j+w+1)) at he
  rw [hmass (i-w) (i+w+1) (by omega),hmass (j-w) (j+w+1) (by omega)] at he
  exact he

/-- Lemma A.9(iii) (`lem:vmono`): the original measure remains feasible with
exactly the source coefficient θ C, including its v=0 convention. -/
theorem feasible_explicit_scale {v v' t C : ℝ} {ν : Spectrum}
    (h : Feasible v t ν C) (hv' : 0 ≤ v') (hvv' : v' ≤ v) :
    Feasible v' t ν ((if v = 0 then 1 else Real.sinh v' / Real.sinh v) * C) := by
  by_cases hv : v = 0
  · have hv'e : v' = 0 := le_antisymm (by simpa only [hv] using hvv') hv'
    simpa only [hv,hv'e,ite_true,one_mul] using h
  · have hvpos : 0 < v := lt_of_le_of_ne (hv'.trans hvv') (Ne.symm hv)
    have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hvpos
    have hθ₀ : 0 ≤ Real.sinh v' / Real.sinh v :=
      div_nonneg (Real.sinh_nonneg_iff.mpr hv') hs.le
    have hθ₁ : Real.sinh v' / Real.sinh v ≤ 1 :=
      (div_le_one hs).mpr (Real.sinh_le_sinh.mpr hvv')
    have hscaled := (show FeasibleU (Real.sinh v) t ν C from h).scale hθ₀ hθ₁
    have he : (Real.sinh v' / Real.sinh v) * Real.sinh v = Real.sinh v' :=
      div_mul_cancel₀ _ hs.ne'
    simpa only [Feasible,ite_eq_right hv,he] using hscaled


open General Levels ModeLocking ModeLocking.Plateaus MeasureTheory
open CertifiedExamples.Plateaus

/-- Theorem 3.16 (`thm:modelock`): the full analytic fixed-support
continuation, with every threshold, extremal, gradient and regularity conclusion
visible in the result type. Continuation and persistence are not hypotheses. -/
theorem mode_locking {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L) :
    ∃ C : D.ContinuationData, ∃ U : Set Tuning,
      IsOpen U ∧ q ∈ U ∧ C.shift (Continuation.parameters q) = s ∧
      (∀ i, C.primal (Continuation.parameters q) i = (D.primal i : ℝ)) ∧
      ∀ q' ∈ U,
        AnalyticAt ℝ C.shift (Continuation.parameters q') ∧
        AnalyticAt ℝ C.primal (Continuation.parameters q') ∧
        (∀ i, 0 < C.primal (Continuation.parameters q') i) ∧
        Threshold.sigma q' = C.shift (Continuation.parameters q') ∧
        Threshold.sigmaPeriodic q' L = C.shift (Continuation.parameters q') ∧
        Continuation.tightDeterminant D.reps D.atoms
          (Continuation.sourcePoint q' (C.shift (Continuation.parameters q'))) = 0 ∧
        ProgramSolution (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q')))
          nonzeroLags (atomicMeasure (C.persistedPrimal q') D.atoms) ∧
        (∀ w : Measure Levels.Frequency,
          ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w ↔
            ∃ c a : NNReal, 0 < c ∧
              w = (c : ENNReal) • atomicMeasure (C.persistedPrimal q') D.atoms +
                (a : ENNReal) • Measure.dirac frequencyZero ∧
              (a : ℝ) ≤ (c : ℝ) * ∫ ω,
                (Geometry.shiftedCurve q' (Threshold.sigma q')).minimizer ω
                  ∂atomicMeasure (C.persistedPrimal q') D.atoms) ∧
        (∃ varpi : Fin D.d → ℝ,
          (∀ i, 0 < varpi i) ∧ (∑ i, varpi i) = 1 ∧
          (∀ v : Continuation.Parameters,
            fderiv ℝ C.shift (Continuation.parameters q') v =
              -∑ i, varpi i * fderiv ℝ (Gradient.sourceCotangent (D.atoms i))
                (Continuation.parameters q') v)) ∧
        fderiv ℝ C.shift (Continuation.parameters q') Gradient.kappaDirection < 0 ∧
        ∃ D' : RegularData q' (C.shift (Continuation.parameters q')) L,
          Set.range D'.atoms = Set.range D.atoms ∧ D'.lags = D.lags := by
  obtain ⟨C,U,ho,hq,hlocal⟩ := D.mode_locking
  refine ⟨C,U,ho,hq,C.shift_base,fun i => C.primal_base i,?_⟩
  intro q' hq'
  obtain ⟨A⟩ := hlocal q' hq'
  refine ⟨analyticAt_fst.comp A.analytic_primalShift,
    analyticAt_snd.comp A.analytic_primalShift,A.persistence.primal_pos,
    A.sigma_eq,A.sigmaPeriodic_eq,A.determinant_zero,A.primal_feasible,
    fun w => A.extremal_iff w,?_,A.kappa_derivative_neg,A.regularData,rfl,rfl⟩
  exact ⟨A.regularData.gradientWeight,A.regularData.gradientWeight_pos,
    A.regularData.gradientWeight_sum,fun v => A.weighted_gradient v⟩

/-- Theorem 3.17 (`thm:plateaus`): all points of the first entire plateau,
not just its certified base point, have exactly the multiples of 18 as periods. -/
theorem first_plateau_periods {r : regularBoundary}
    (hr : r.val ∈ plateau boundary18.val) (k : ℕ) :
    PeriodicFP (tuningCurve r.val.val) k ↔ 18 ∣ k := by
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have hs : Set.range R.atoms = Set.range row18_regularData.atoms := by
    exact (support_constant_on_plateau hr).trans (regularBoundaryPoint_support row18_regularData)
  have hzero : Threshold.sigma r.val.val = 0 :=
    (mem_frontier_iff_sigma_zero r.val.val).mp r.val.property
  have he : PeriodicFP (tuningCurve r.val.val) k ↔
      ∀ i, R.atoms i ∈ periodicGrid k := by
    calc
      _ ↔ PeriodicFP (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)) k := by
        rw [hzero,Geometry.shiftedCurve_zero]
      _ ↔ _ := R.periodic_iff_support k
  rw [he,←row18_regularData.support_period_iff_dvd k]
  constructor
  · intro h i
    obtain ⟨j,hj⟩ := hs.symm ▸ Set.mem_range_self i
    exact hj ▸ h j
  · intro h i
    obtain ⟨j,hj⟩ := hs ▸ Set.mem_range_self i
    exact hj ▸ h j

/-- Theorem 3.17 (`thm:plateaus`): every extremal throughout the second
plateau has positive mass at each of its three nonzero frequencies and no
other positive frequency. The admissible zero atom is retained. -/
theorem second_plateau_support {r : regularBoundary}
    (hr : r.val ∈ plateau boundary21.val) {w : Measure Levels.Frequency}
    (hw : ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    (∀ᵐ ω ∂w, ω = frequencyZero ∨ ω ∈ Set.range atoms21) ∧
      ∀ i : Fin 3, 0 < w {atoms21 i} := by
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have hs : Set.range R.atoms = Set.range atoms21 := by
    exact (support_constant_on_plateau hr).trans (regularBoundaryPoint_support row21_regularData)
  have hzero : Threshold.sigma r.val.val = 0 :=
    (mem_frontier_iff_sigma_zero r.val.val).mp r.val.property
  have hsol : ProgramSolution (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val))
      nonzeroLags w := by simpa only [hzero,Geometry.shiftedCurve_zero] using hw
  constructor
  · filter_upwards [R.program_carried (fun n hn => R.lags_nonzero n hn) hsol] with ω hω
    rcases hω with h0 | ⟨i,rfl⟩
    · exact Or.inl h0
    · exact Or.inr (hs ▸ Set.mem_range_self i)
  · intro i
    obtain ⟨j,hj⟩ := hs.symm ▸ Set.mem_range_self i
    obtain ⟨c,a,hc,he,_⟩ := R.extremal_classification
      (fun n hn => R.lags_nonzero n hn) hsol
    rw [he,←hj]
    have hp : 0 < ((c:ENNReal) • R.measure) {R.atoms j} := by
      rw [Measure.smul_apply,smul_eq_mul]
      exact ENNReal.mul_pos_iff.mpr ⟨by exact_mod_cast hc,
        atomicMeasure_atom_pos R.primal R.atoms j (R.primal_pos j)⟩
    exact hp.trans_le (Measure.le_add_right (le_refl ((c:ENNReal) • R.measure)) _)

end polyak.ArticleResults
