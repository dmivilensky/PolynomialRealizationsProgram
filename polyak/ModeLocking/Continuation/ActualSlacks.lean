import polyak.ModeLocking.Continuation.Family
import polyak.ModeLocking.Continuation.Rank

/-! Strict inactive and minimizer slacks persist for the actual tuning
topology, including its momentum-zero boundary. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General

theorem continuous_parameters : Continuous parameters := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Tuning.continuous_kappa
  · exact Tuning.continuous_y
  · exact Tuning.continuous_beta

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

theorem continuousAt_shift_actual : ContinuousAt (fun q' : Tuning => C.shift (Continuation.parameters q')) q :=
  (analyticAt_fst.comp (f := C.primalShift) C.analytic_primalShift).continuousAt.comp
    Continuation.continuous_parameters.continuousAt

theorem continuousAt_primal_actual (i : Fin D.d) :
    ContinuousAt (fun q' : Tuning => C.primal (Continuation.parameters q') i) q := by
  have hc : ContinuousAt (fun p => C.primal p i) (Continuation.parameters q) :=
    (continuous_apply i).continuousAt.comp C.analytic_primalShift.continuousAt.snd
  exact hc.comp Continuation.continuous_parameters.continuousAt

theorem continuousAt_phase_actual (i : Fin D.d) : ContinuousAt (fun q' : Tuning =>
    Geometry.shiftedCurve q' (C.shift (Continuation.parameters q')) (D.atoms i)) q := by
  have hp : ContinuousAt (fun q' : Tuning => ((q', C.shift (Continuation.parameters q')), D.atoms i)) q :=
    (continuousAt_id.prodMk C.continuousAt_shift_actual).prodMk continuousAt_const
  exact Threshold.shiftedCurve_jointContinuous.continuousAt.comp
    (f := fun q' : Tuning => ((q', C.shift (Continuation.parameters q')), D.atoms i)) hp

theorem continuousAt_lag_actual (n : ℤ) (i : Fin D.d) : ContinuousAt (fun q' : Tuning =>
    (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q'))).lag n (D.atoms i)) q := by
  exact (Real.continuous_cos.continuousAt.comp (C.continuousAt_phase_actual i)).sub
    (Real.continuous_cos.continuousAt.comp (continuousAt_const.sub (C.continuousAt_phase_actual i)))

theorem primal_base (i : Fin D.d) : C.primal (Continuation.parameters q) i = (D.primal i : ℝ) :=
  congrArg (fun z : ℝ × (Fin D.d → ℝ) => z.2 i) C.primalShift_base

def lagSlack (q' : Tuning) (n : ℤ) : ℝ := ∑ i,
  C.primal (Continuation.parameters q') i *
    (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q'))).lag n (D.atoms i)

def minimizerSlack (q' : Tuning) : ℝ := ∑ i,
  C.primal (Continuation.parameters q') i *
    (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q'))).minimizer (D.atoms i)

theorem continuousAt_lagSlack (n : ℤ) : ContinuousAt (fun q' => C.lagSlack q' n) q :=
  tendsto_finsetSum Finset.univ (fun i _ => (C.continuousAt_primal_actual i).mul (C.continuousAt_lag_actual n i))

theorem continuousAt_minimizerSlack : ContinuousAt C.minimizerSlack q :=
  tendsto_finsetSum Finset.univ (fun i _ => (C.continuousAt_primal_actual i).mul
    (Real.continuous_cos.continuousAt.comp (C.continuousAt_phase_actual i)))

theorem minimizerSlack_pos : ∀ᶠ q' in 𝓝 q, 0 < C.minimizerSlack q' := by
  apply C.continuousAt_minimizerSlack.eventually
  apply eventually_gt_nhds
  simpa only [minimizerSlack, C.primal_base, C.shift_base] using D.minimizer_strict

theorem inactiveSlacks_pos : ∀ᶠ q' in 𝓝 q, ∀ r : ℤ, 0 < r → r < L →
    (∀ i, r ≠ D.reps i) → 0 < C.lagSlack q' r := by
  classical
  have he (r : ℤ) (hr : r ∈ Finset.Ioo (0 : ℤ) (L : ℤ)) :
      ∀ᶠ q' in 𝓝 q, (∀ i, r ≠ D.reps i) → 0 < C.lagSlack q' r := by
    by_cases ht : ∀ i, r ≠ D.reps i
    · have hpos : 0 < C.lagSlack q r := by
        simpa only [lagSlack, C.primal_base, C.shift_base] using
          D.inactive r (Finset.mem_Ioo.mp hr).1 (Finset.mem_Ioo.mp hr).2 ht
      exact (C.continuousAt_lagSlack r).eventually (eventually_gt_nhds hpos) |>.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (ht h).elim)
  have hall : ∀ᶠ q' in 𝓝 q, ∀ r ∈ Finset.Ioo (0 : ℤ) (L : ℤ),
      (∀ i, r ≠ D.reps i) → 0 < C.lagSlack q' r := by
    rw [Filter.eventually_all_finset]
    exact he
  filter_upwards [hall] with q' hq' r hr hrL ht
  exact hq' r (Finset.mem_Ioo.mpr ⟨hr, hrL⟩) ht

end polyak.ModeLocking.RegularData.ContinuationData
