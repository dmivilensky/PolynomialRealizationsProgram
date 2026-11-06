import nesterov.Smooth.Execution
import nesterov.Rates.Envelope
import nesterov.Stationary.FiniteSpan

/-!
Article: Remark `rem:uniform-smoothness`, Appendix A.
Use: finite-dimensional C∞ objectives have exactly the same finite-horizon
uniform envelopes. Suprema are compared only after boundedness is established.
-/
namespace nesterov.Rates
noncomputable section
open Set Filter
open scoped Topology ContDiff

/-- Ratios attained by actual finite-dimensional infinitely smooth objectives. -/
def smoothRatios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, ∃ _ : FiniteDimensional ℝ r.Carrier,
    ContDiff ℝ ∞ r.f ∧ r.stateNorm 0 ≠ 0 ∧ x=r.stateNorm n/r.stateNorm 0}

/-- The finite-horizon supremum restricted to genuine finite-dimensional C∞ objectives. -/
def smoothEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (smoothRatios M μ L n))

theorem smoothRatios_subset (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    smoothRatios M μ L n ⊆ ratios M μ L n := by
  rintro x ⟨r,_,_,hr,hx⟩
  exact ⟨r,hr,hx⟩

theorem smoothRatios_bddAbove (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    BddAbove (insert 0 (smoothRatios M μ L n)) :=
  (ratios_bddAbove M μ L n).mono (insert_subset_insert (smoothRatios_subset M μ L n))

theorem smoothEnvelope_nonneg (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    0 ≤ smoothEnvelope M μ L n :=
  le_csSup (smoothRatios_bddAbove M μ L n) (mem_insert _ _)

theorem smoothEnvelope_le_envelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    smoothEnvelope M μ L n ≤ envelope M μ L n :=
  csSup_le_csSup (ratios_bddAbove M μ L n) (insert_nonempty _ _)
    (insert_subset_insert (smoothRatios_subset M μ L n))

/-- Every finite-dimensional C¹,¹ ratio is a limit of C∞ ratios, with exactly the
same initial memory. Thus smoothing preserves every finite-horizon supremum. -/
theorem finiteDimensional_ratio_le_smoothEnvelope {M : StationaryMethod} {μ L : ℝ}
    (r : HilbertRun M μ L) [FiniteDimensional ℝ r.Carrier]
    (hr : r.stateNorm 0 ≠ 0) (n : ℕ) :
    r.stateNorm n/r.stateNorm 0 ≤ smoothEnvelope M μ L n := by
  borelize r.Carrier
  let initial : Fin M.memory → r.Carrier := fun j => r.w j
  obtain ⟨fs,hclass,_,hlim⟩ := nesterov.Smooth.exists_smooth_runs
    MeasureTheory.Measure.addHaar M r.admissible initial
  let s (i : ℕ) : HilbertRun M μ L :=
    ⟨r.Carrier,fs i,(hclass i).1,M.run (gradient (fs i)) initial,M.run_isTrajectory _ _⟩
  have hi0 (i : ℕ) : (s i).stateNorm 0=r.stateNorm 0 := by
    change M.stateNorm (M.run (gradient (fs i)) initial) 0=M.stateNorm r.w 0
    unfold StationaryMethod.stateNorm
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.zero_add,M.run_initial,initial]
  have hbound (i : ℕ) : (s i).stateNorm n/r.stateNorm 0 ≤ smoothEnvelope M μ L n := by
    apply le_csSup (smoothRatios_bddAbove M μ L n)
    apply mem_insert_of_mem
    exact ⟨s i,inferInstance,(hclass i).2,by rwa [hi0],by rw [hi0]⟩
  have hprefix : ∀ k, Tendsto (fun i => M.run (gradient (fs i)) initial k) atTop (𝓝 (r.w k)) := by
    intro k
    have h := hlim k
    have he := r.trajectory.eq_run M
    rw [he]
    exact h
  have hnorm := nesterov.Smooth.stateNorm_tendsto M hprefix n
  have hratio := hnorm.div_const (r.stateNorm 0)
  exact le_of_tendsto hratio (Eventually.of_forall hbound)

/-- The literal all-Hilbert finite-horizon supremum equals its restriction to
finite-dimensional C∞ objectives, with exactly the same μ,L parameters. -/
theorem smoothEnvelope_eq_envelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    smoothEnvelope M μ L n=envelope M μ L n := by
  apply le_antisymm (smoothEnvelope_le_envelope M μ L n)
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hr,rfl⟩
  · exact smoothEnvelope_nonneg M μ L n
  · obtain ⟨s,hfd,hs⟩ := r.exists_finiteDimensional_prefix n
    let _ : FiniteDimensional ℝ s.Carrier := hfd
    have hr' : s.stateNorm 0 ≠ 0 := by rwa [hs 0 (Nat.zero_le _)]
    rw [← hs 0 (Nat.zero_le _),← hs n le_rfl]
    exact finiteDimensional_ratio_le_smoothEnvelope s hr' n

end
end nesterov.Rates
