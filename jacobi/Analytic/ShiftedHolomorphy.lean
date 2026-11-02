import jacobi.Analytic.ShiftedProfiles

/-!
Article: jacobi, Theorem C.5.
The actual original shifted profile is holomorphic in its parameter
on the full source slit plane and continuous in its physical variable.
The locally uniform majorants are proved for the actual original series.
Source: the Weierstrass theorem for holomorphic series.
Use: Theorem C.5's genuine shifted squared-profile integrals are integrals of this actual continuous function, including at the reflected physical endpoints.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.GelfandLevitan jacobi.Reference
open scoped Topology

/-- The genuine original shifted profile is continuous on the whole closed physical interval for every original admissible complex shift.
Use: Theorem C.5's genuine shifted squared-profile integrals are integrals of this actual continuous function, including at the reflected physical endpoints.
Article: jacobi, Theorem C.5.
Source: uniform limits of continuous functions.
Proof: the original singleton shift set has the proved uniform summable profile majorant. Every actual original spectral profile is continuous, so the genuine uniform series limit is continuous on the full physical interval. -/
theorem shiftedProfile_continuous (a:ℝ) (ha:-1<a) {w:ℂ} (hw:w∈edgeDomain a ha) :
    Continuous (fun t:Interval => shiftedProfile a ha t w) := by
  -- The same actual source series converges uniformly over all physical points, before continuity of its sum is asserted.
  obtain ⟨C,hC,hbound⟩ := shiftedProfile_majorant a ha (W:={w}) isCompact_singleton
    (by simpa only [singleton_subset_iff] using hw)
  have hu := tendstoUniformly_tsum_nat ((jacobi.Bessel.edgeValue_summable ha).mul_left C)
    (f:=fun k:ℕ => fun t:Interval => shiftedProfileTerm a ha k t w)
    (fun k t => hbound k t w (mem_singleton w))
  apply hu.continuous
  apply Filter.Eventually.frequently
  exact Eventually.of_forall (fun N => by
    apply continuous_finsetSum
    intro k _hk
    unfold shiftedProfileTerm
    fun_prop)

/-- The actual original shifted profile is holomorphic throughout its complete original slit domain.
Use: Theorem C.5's holomorphic profile assertion and shifted energy analysis use the same genuine source series and the same actual transformed spectral profiles from Proposition C.2.
Article: jacobi, Theorem C.5.
Source: locally uniform limits of holomorphic series, mathlib differentiableOn_tsum_of_summable_norm.
Proof: around each genuine domain point choose a smaller closed disc contained in the actual open slit plane. Its proved original compact spectral majorant bounds every genuine holomorphic term by the same summable Rayleigh sequence. The community Weierstrass theorem makes the original series differentiable on that disc and hence at the arbitrary original domain point. -/
theorem shiftedProfile_holomorphic (a:ℝ) (ha:-1<a) (t:Interval) :
    DifferentiableOn ℂ (shiftedProfile a ha t) (edgeDomain a ha) := by
  -- A common compact majorant for the actual original terms supplies norm differentiability, not only a formal termwise complex derivative.
  intro w hw
  have hU : IsOpen (edgeDomain a ha) := slitDomain_open _
  obtain ⟨delta,hdelta,hball⟩ := Metric.isOpen_iff.mp hU w hw
  let r := delta/2
  have hr : 0<r := by dsimp [r]; positivity
  have hclosed : Metric.closedBall w r⊆edgeDomain a ha :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hball
  obtain ⟨C,hC,hbound⟩ := shiftedProfile_majorant a ha (isCompact_closedBall w r) hclosed
  have hterms (k:ℕ) : DifferentiableOn ℂ (fun z:ℂ => shiftedProfileTerm a ha k t z) (Metric.ball w r) := by
    intro z hz
    exact ((shiftedEdge_analytic a ha k (hclosed (Metric.ball_subset_closedBall hz))).differentiableAt.mul_const
      (spectralProfile a ha k t:ℂ)).differentiableWithinAt
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    ((jacobi.Bessel.edgeValue_summable ha).mul_left C) hterms Metric.isOpen_ball
    (fun k z hz => hbound k t z (Metric.ball_subset_closedBall hz))
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- The genuine original shifted resolvent profile has one uniform bound on the complete physical interval times every compact original shift set.
Use: Theorem C.5's shifted integrals and eventual finite comparison use this actual continuum uniform bound, with the original positive Rayleigh mass already evaluated.
Article: jacobi, Theorem C.5.
Proof: the actual norm-convergent original series is bounded by its summed genuine compact spectral majorant. The independently proved first Rayleigh sum evaluates that bound exactly, and the full original parameter range makes it strictly positive. -/
theorem shiftedProfile_compact_bound (a:ℝ) (ha:-1<a) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆edgeDomain a ha) :
    ∃B:ℝ,0<B ∧ ∀t:Interval,∀w∈W,‖shiftedProfile a ha t w‖≤B := by
  -- The compact bound is a genuine summed Rayleigh majorant for the same original shifted profile.
  obtain ⟨C,hC,hbound⟩ := shiftedProfile_majorant a ha hW hsub
  refine ⟨C/(2*(a+1)),div_pos hC (by linarith),?_⟩
  intro t w hw
  have hnorm := shiftedProfile_norm_summable a ha t (hsub hw)
  calc
    _ ≤ ∑'k:ℕ,‖shiftedProfileTerm a ha k t w‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑'k:ℕ,C* jacobi.Bessel.edgeValue a ha k :=
      hnorm.tsum_le_tsum (fun k => hbound k t w hw) ((jacobi.Bessel.edgeValue_summable ha).mul_left C)
    _ = _ := by rw [tsum_mul_left,jacobi.Bessel.first_rayleigh_sum ha]; ring

end
end jacobi.EdgeResolvent
