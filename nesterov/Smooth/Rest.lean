import nesterov.Smooth.Envelope

/-!
Article: Definition `def:rate` and Remark `rem:uniform-smoothness`.
Use: literal finite-dimensional from-rest suprema and their exact invariance
under restricting objectives to C∞. A rest state has every latent slot equal.
-/
namespace nesterov.Rates
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators

/-- An execution starts from rest when the whole initial memory is constant. -/
def HilbertRun.FromRest {M : StationaryMethod} {μ L : ℝ} (r : HilbertRun M μ L) : Prop :=
  ∀ j : Fin M.memory, r.w j=r.w 0

/-- Literal from-rest ratios in finite dimension, read at the latest state coordinate. -/
def restRatios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, ∃ _ : FiniteDimensional ℝ r.Carrier,
    r.FromRest ∧ r.w 0 ≠ 0 ∧ x=‖r.w (n+M.memory-1)‖/‖r.w 0‖}

/-- The exact finite-horizon from-rest distance envelope. -/
def restEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (restRatios M μ L n))

/-- The same actual from-rest ratios restricted to C∞ objectives. -/
def smoothRestRatios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, ∃ _ : FiniteDimensional ℝ r.Carrier,
    ContDiff ℝ ∞ r.f ∧ r.FromRest ∧ r.w 0 ≠ 0 ∧ x=‖r.w (n+M.memory-1)‖/‖r.w 0‖}

/-- The finite-horizon C∞ from-rest distance envelope. -/
def smoothRestEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (smoothRestRatios M μ L n))

/-- The full initial state has norm √D times the common nonzero initial displacement. -/
theorem HilbertRun.FromRest.stateNorm_zero {M : StationaryMethod} {μ L : ℝ}
    {r : HilbertRun M μ L} (hr : r.FromRest) :
    r.stateNorm 0=Real.sqrt M.memory*‖r.w 0‖ := by
  change Real.sqrt (∑ j : Fin M.memory, ‖r.w (0+j)‖^2)=_
  change ∀ j : Fin M.memory, r.w j=r.w 0 at hr
  simp only [Nat.zero_add,hr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (norm_nonneg _)]

/-- From-rest distance is controlled by the genuine free-state envelope. -/
theorem fromRest_ratio_le_envelope {M : StationaryMethod} {μ L : ℝ}
    (r : HilbertRun M μ L) (hr : r.FromRest) (hz : r.w 0 ≠ 0) (n : ℕ) :
    ‖r.w (n+M.memory-1)‖/‖r.w 0‖ ≤ Real.sqrt M.memory*envelope M μ L n := by
  have hn := M.norm_le_stateNorm r.w n (⟨M.memory-1,by have := M.memory_pos; omega⟩ : Fin M.memory)
  have he : n+(M.memory-1)=n+M.memory-1 := by have := M.memory_pos; omega
  rw [he] at hn
  have hs := stateNorm_le_envelope r n
  rw [hr.stateNorm_zero] at hs
  apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
  change ‖r.w (n+M.memory-1)‖ ≤ r.stateNorm n at hn
  nlinarith

theorem restRatios_bddAbove (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    BddAbove (insert 0 (restRatios M μ L n)) := by
  refine ⟨Real.sqrt M.memory*envelope M μ L n,?_⟩
  intro x hx
  rcases hx with rfl | ⟨r,_,hr,hz,rfl⟩
  · exact mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg M μ L n)
  · exact fromRest_ratio_le_envelope r hr hz n

theorem restEnvelope_nonneg (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    0 ≤ restEnvelope M μ L n :=
  le_csSup (restRatios_bddAbove M μ L n) (mem_insert _ _)

theorem restEnvelope_le_envelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    restEnvelope M μ L n ≤ Real.sqrt M.memory*envelope M μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,_,hr,hz,rfl⟩
  · exact mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg M μ L n)
  · exact fromRest_ratio_le_envelope r hr hz n

theorem smoothRestRatios_subset (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    smoothRestRatios M μ L n ⊆ restRatios M μ L n := by
  rintro x ⟨r,hfd,_,hr,hz,hx⟩
  exact ⟨r,hfd,hr,hz,hx⟩

theorem smoothRestRatios_bddAbove (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    BddAbove (insert 0 (smoothRestRatios M μ L n)) :=
  (restRatios_bddAbove M μ L n).mono (insert_subset_insert (smoothRestRatios_subset M μ L n))

theorem smoothRestEnvelope_nonneg (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    0 ≤ smoothRestEnvelope M μ L n :=
  le_csSup (smoothRestRatios_bddAbove M μ L n) (mem_insert _ _)

/-- Every actual from-rest ratio is approximated with its exact same initial point. -/
theorem fromRest_ratio_le_smoothRestEnvelope {M : StationaryMethod} {μ L : ℝ}
    (r : HilbertRun M μ L) [FiniteDimensional ℝ r.Carrier]
    (hr : r.FromRest) (hz : r.w 0 ≠ 0) (n : ℕ) :
    ‖r.w (n+M.memory-1)‖/‖r.w 0‖ ≤ smoothRestEnvelope M μ L n := by
  borelize r.Carrier
  let initial : Fin M.memory → r.Carrier := fun _ => r.w 0
  obtain ⟨fs,hclass,_,hlim⟩ := nesterov.Smooth.exists_smooth_runs
    MeasureTheory.Measure.addHaar M r.admissible initial
  let s (i : ℕ) : HilbertRun M μ L :=
    ⟨r.Carrier,fs i,(hclass i).1,M.run (gradient (fs i)) initial,M.run_isTrajectory _ _⟩
  have hi0 (i : ℕ) : (s i).w 0=r.w 0 :=
    M.run_initial _ initial ⟨0,M.memory_pos⟩
  have hrest (i : ℕ) : (s i).FromRest := by
    intro j
    change M.run (gradient (fs i)) initial j=(s i).w 0
    rw [M.run_initial,hi0]
  have hbound (i : ℕ) : ‖(s i).w (n+M.memory-1)‖/‖r.w 0‖ ≤
      smoothRestEnvelope M μ L n := by
    apply le_csSup (smoothRestRatios_bddAbove M μ L n)
    apply mem_insert_of_mem
    exact ⟨s i,inferInstance,(hclass i).2,hrest i,by rwa [hi0],by rw [hi0]⟩
  have hbase : r.w=M.run (gradient r.f) initial :=
    StationaryMethod.IsTrajectory.unique M r.trajectory (M.run_isTrajectory _ _)
      (fun j => (hr j).trans (M.run_initial _ initial j).symm)
  have hprefix := hlim (n+M.memory-1)
  rw [← hbase] at hprefix
  exact le_of_tendsto (hprefix.norm.div_const ‖r.w 0‖) (Eventually.of_forall hbound)

/-- At every finite horizon the C∞ restriction leaves the literal from-rest
supremum unchanged. No horizon-dependent initialization is introduced. -/
theorem smoothRestEnvelope_eq_restEnvelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    smoothRestEnvelope M μ L n=restEnvelope M μ L n := by
  apply le_antisymm
  · exact csSup_le_csSup (restRatios_bddAbove M μ L n) (insert_nonempty _ _)
      (insert_subset_insert (smoothRestRatios_subset M μ L n))
  · apply csSup_le (insert_nonempty _ _)
    intro x hx
    rcases hx with rfl | ⟨r,hfd,hr,hz,rfl⟩
    · exact smoothRestEnvelope_nonneg M μ L n
    · let _ : FiniteDimensional ℝ r.Carrier := hfd
      exact fromRest_ratio_le_smoothRestEnvelope r hr hz n

end
end nesterov.Rates
