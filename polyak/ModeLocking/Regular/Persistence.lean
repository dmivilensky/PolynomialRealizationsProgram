import polyak.ModeLocking.Continuation.SignPersistence
import polyak.ModeLocking.Continuation.FiniteConditions

/-! Full persistence of all literal primary regularity conditions, with
the original atoms, tight residues, and signed-lag set kept fixed. -/
noncomputable section
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter Set
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

structure PersistenceFacts (q' : Tuning) where
  right_kernel : (D.continuedMatrix C.primalShift (Continuation.parameters q')).mulVec (C.primal (Continuation.parameters q')) = 0
  primal_sum : (∑ i, C.primal (Continuation.parameters q') i) = 1
  primal_pos : ∀ i, 0 < C.primal (Continuation.parameters q') i
  dual_sum : (∑ n ∈ D.lags, C.weight (Continuation.parameters q') n) = 1
  dual_pos : ∀ n ∈ D.lags, 0 < C.weight (Continuation.parameters q') n
  rank : (D.continuedMatrix C.primalShift (Continuation.parameters q')).rank = D.d - 1
  inactive : ∀ r : ℤ, 0 < r → r < L → (∀ i, r ≠ D.reps i) → 0 < C.lagSlack q' r
  minimizer : 0 < C.minimizerSlack q'
  pinning : ∀ i, 0 < pinningPolynomial D.lags (C.weight (Continuation.parameters q')) (D.atoms i)
  pinning_det : (C.actualPinning q').det ≠ 0
  cover : Analysis.NegativeJetCover 0 Real.pi D.zeroCenters
    (finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags (C.weight (Continuation.parameters q')))

theorem persistenceFacts_near : ∀ᶠ q' in 𝓝 q, Nonempty (C.PersistenceFacts q') := by
  have hq := Continuation.continuous_parameters.continuousAt.eventually C.equations
  have hw := Continuation.continuous_parameters.continuousAt.eventually C.weight_sum
  have hp := Continuation.continuous_parameters.continuousAt.eventually C.weight_pos
  have hr := Continuation.continuous_parameters.continuousAt.eventually C.matrix_rank
  filter_upwards [hq, hw, hp, hr, C.inactiveSlacks_pos, C.minimizerSlack_pos,
    C.pinning_pos_near, C.pinning_det_near, C.negative_cover_near] with q' hq' hw' hp' hr' hi hm hP hdet hcover
  obtain ⟨B⟩ := hcover
  exact ⟨⟨hq'.1, hq'.2.2.1, hq'.2.2.2.2.2.1, hw', hp', hr', hi, hm, hP, hdet, B⟩⟩

def persistedPrimal (q' : Tuning) : Fin D.d → NNReal :=
  fun i => Real.toNNReal (C.primal (Continuation.parameters q') i)

theorem persistedPrimal_coe {q' : Tuning} (F : C.PersistenceFacts q') (i : Fin D.d) :
    (C.persistedPrimal q' i : ℝ) = C.primal (Continuation.parameters q') i :=
  Real.coe_toNNReal _ (F.primal_pos i).le

def persistedData (q' : Tuning) (F : C.PersistenceFacts q') :
    RegularData q' (C.shift (Continuation.parameters q')) L where
  period_ge := D.period_ge
  d := D.d
  atoms := D.atoms
  atoms_injective := D.atoms_injective
  atoms_grid := D.atoms_grid
  atoms_lt_pi := D.atoms_lt_pi
  reps := D.reps
  reps_pos := D.reps_pos
  reps_lt := D.reps_lt
  reps_injective := D.reps_injective
  lags := D.lags
  lags_nonzero := D.lags_nonzero
  classes := D.classes
  primal := C.persistedPrimal q'
  primal_pos := by
    intro i
    exact_mod_cast (show 0 < (C.persistedPrimal q' i : ℝ) by rw [C.persistedPrimal_coe F]; exact F.primal_pos i)
  primal_sum := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, C.persistedPrimal_coe F, NNReal.coe_one] using F.primal_sum
  dual := C.weight (Continuation.parameters q')
  dual_pos := F.dual_pos
  dual_sum := F.dual_sum
  tight := by
    intro r
    have he := congrFun F.right_kernel r
    change (∑ i, Continuation.ambientLag (D.reps r) (D.atoms i)
      (Continuation.sourcePoint q' (C.shift (Continuation.parameters q'))) * C.primal (Continuation.parameters q') i) = 0 at he
    simpa only [C.persistedPrimal_coe F, Continuation.ambientLag_actual, mul_comm] using he
  inactive := by
    intro r hr hrL ht
    simpa only [lagSlack, C.persistedPrimal_coe F] using F.inactive r hr hrL ht
  minimizer_strict := by
    simpa only [minimizerSlack, C.persistedPrimal_coe F] using F.minimizer
  rank := by
    have he : D.continuedMatrix C.primalShift (Continuation.parameters q') =
        (fun r i : Fin D.d => (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q'))).lag (D.reps r) (D.atoms i)) := by
      ext r i
      exact Continuation.ambientLag_actual q' (C.shift (Continuation.parameters q')) (D.reps r) (D.atoms i)
    rw [← he]
    exact F.rank
  dual_strict := by
    intro x hx hxpi hneq
    apply F.cover.strict ⟨hx.le, hxpi⟩
    intro hz
    rcases (D.mem_zeroCenters x).mp hz with he | ⟨i, hi⟩
    · exact hx.ne' he
    · exact hneq i hi
  support_curvature := by
    intro i
    have hz : (D.atoms i : ℝ) ∈ D.zeroCenters := (D.mem_zeroCenters _).mpr (Or.inr ⟨i, rfl⟩)
    have he := F.cover.local_bound (D.atoms i) hz (D.atoms i) (D.atoms i).property
      (by simp only [sub_self, abs_zero]; exact F.cover.radius_pos.le)
    rw [iteratedDeriv_eq_iterate] at he
    exact he.trans_lt (neg_neg_of_pos F.cover.curvature_pos)
  endpoint_curvature := by
    have hz : (0 : ℝ) ∈ D.zeroCenters := (D.mem_zeroCenters 0).mpr (Or.inl rfl)
    have he := F.cover.local_bound 0 hz 0 ⟨le_rfl, Real.pi_pos.le⟩
      (by simp only [sub_self, abs_zero]; exact F.cover.radius_pos.le)
    rw [iteratedDeriv_eq_iterate, finiteSymbol_second_zero] at he
    linarith [F.cover.curvature_pos]
  pinning_pos := F.pinning
  class_pair := D.class_pair
  pinning_det := F.pinning_det

theorem data_near : ∀ᶠ q' in 𝓝 q,
    ∃ D' : RegularData q' (C.shift (Continuation.parameters q')) L,
      Set.range D'.atoms = Set.range D.atoms ∧ Set.range D'.reps = Set.range D.reps ∧ D'.lags = D.lags := by
  filter_upwards [C.persistenceFacts_near] with q' hq'
  obtain ⟨F⟩ := hq'
  exact ⟨C.persistedData q' F, rfl, rfl, rfl⟩

theorem shift_eq_sigma : ∀ᶠ q' in 𝓝 q, C.shift (Continuation.parameters q') = Threshold.sigma q' := by
  filter_upwards [C.data_near] with q' hq'
  obtain ⟨D', _⟩ := hq'
  exact D'.sigma_eq.symm

end polyak.ModeLocking.RegularData.ContinuationData

namespace polyak.ModeLocking.RegularData
open General Levels Filter Set
open scoped Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem regular_persistence : ∀ᶠ q' in 𝓝 q,
    ∃ D' : RegularData q' (Threshold.sigma q') L,
      Set.range D'.atoms = Set.range D.atoms ∧ Set.range D'.reps = Set.range D.reps ∧ D'.lags = D.lags := by
  obtain ⟨C⟩ := D.continuationData_nonempty
  filter_upwards [C.data_near, C.shift_eq_sigma] with q' hq' he
  rw [he] at hq'
  exact hq'

end polyak.ModeLocking.RegularData
