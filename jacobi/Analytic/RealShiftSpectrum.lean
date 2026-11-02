import jacobi.Analytic.ShiftedSpectrum

/-!
Article: jacobi, Corollary C.6.
For every real shift above the actual first negative spectral pole, the
original shifted Bessel coefficients form a genuine positive summable
edge spectrum. Thus the existing calibrations apply directly to these
actual coefficients without an additional spectral-data hypothesis.
Use: realShiftSpectrum supplies the existing variational calibration interface with the genuine shifted coefficients from Theorem C.5.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The article's actual shifted edge eigenvalue at a real spectral shift.
Use: realShiftSpectrum supplies the existing variational calibration interface with the genuine shifted coefficients from Theorem C.5.
Article: jacobi, Corollary C.6.
-/
def realShiftedEdge (a:ℝ) (ha:-1<a) (w:ℝ) (k:ℕ) : ℝ :=
  2/(jacobi.Bessel.sigma a ha k+w)

/-- Every original real shifted spectral denominator is positive above the genuine first pole.
Use: realShiftedEdge_pos and realShiftSpectrum establish all positivity and order premises of the existing edge-spectrum calibrations.
Article: jacobi, Corollary C.6.
Proof: every actual squared Bessel zero is at least the genuine first squared zero. -/
theorem realShifted_denominator_pos (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) (k:ℕ) : 0< jacobi.Bessel.sigma a ha k+w := by
  have h := (jacobi.Bessel.sigma_strictMono ha).monotone (Nat.zero_le k)
  linarith

/-- Every actual original shifted edge eigenvalue is strictly positive on the full physical real-shift range.
Use: realShiftSpectrum is an actual edge spectrum for every original real shift, so every earlier lower calibration has its true required positive spectral data.
Article: jacobi, Corollary C.6.
Proof: its numerator is two and its actual denominator has the independently proved positive spectral margin. -/
theorem realShiftedEdge_pos (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) (k:ℕ) : 0<realShiftedEdge a ha w k :=
  div_pos (by norm_num) (realShifted_denominator_pos a ha hw k)

/-- The actual original real shifted edge values are summable throughout their full source range.
Use: realShiftSpectrum packages the genuine shifted spectrum without assuming its mass convergence, and shiftedMass_hasDerivAt later differentiates that actual convergent mass series.
Article: jacobi, Corollary C.6.
Proof: embed the real shift in the original slit domain and apply the already proved compact spectral bound to its singleton. The actual original Bessel first Rayleigh series is summable, so it dominates this same positive real shifted sequence. -/
theorem realShiftedEdge_summable (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) : Summable (realShiftedEdge a ha w) := by
  -- This is the genuine shifted spectrum, rather than a stipulated finite-mass replacement.
  have hwC : (w:ℂ)∈edgeDomain a ha := Or.inr hw
  obtain ⟨C,hC,hbound⟩ := shiftedEdge_compact_bound a ha (W:={(w:ℂ)}) isCompact_singleton
    (by intro z hz; exact (mem_singleton_iff.mp hz) ▸ hwC)
  apply ((jacobi.Bessel.edgeValue_summable ha).mul_left C).of_nonneg_of_le
    (fun k => (realShiftedEdge_pos a ha hw k).le)
  intro k
  have h := hbound k (w:ℂ) (mem_singleton _)
  have he : shiftedEdge a ha k (w:ℂ)=(realShiftedEdge a ha w k:ℂ) := by
    unfold shiftedEdge realShiftedEdge
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (realShiftedEdge_pos a ha hw k)] at h
  exact h

/-- The actual shifted Bessel values are a genuine edge spectrum for every real shift above the original first pole.
Use: the existing Young, Keller, root-mass and Fredholm calibrations apply to Lambda(w) in Two-sided bounds off the edge without repeating their variational proofs.
Article: jacobi, Corollary C.6.
-/
def realShiftSpectrum (a:ℝ) (ha:-1<a) (w:ℝ) (hw: - jacobi.Bessel.sigma a ha 0<w) :
    jacobi.Variational.EdgeSpectrum where
  value := realShiftedEdge a ha w
  positive := realShiftedEdge_pos a ha hw
  antitone := by
    intro i j hij
    apply div_le_div_of_nonneg_left (by norm_num) (realShifted_denominator_pos a ha hw i)
    have h := (jacobi.Bessel.sigma_strictMono ha).monotone hij
    linarith
  summable := realShiftedEdge_summable a ha hw

/-- Zero shift recovers the actual original Bessel edge spectrum in the same variational interface.
Use: the original mass and second Rayleigh constants are also the unshifted values of the genuine off-edge calibration problem.
Article: jacobi, Corollary C.6.
Proof: both records have the same actual original spectral values; their positivity, order and convergence proofs are propositions. -/
theorem realShiftSpectrum_zero (a:ℝ) (ha:-1<a) :
    realShiftSpectrum a ha 0 (by have := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0); linarith)=
      jacobi.Bessel.edgeSpectrum a ha := by
  unfold realShiftSpectrum jacobi.Bessel.edgeSpectrum
  congr 1
  funext k
  simp only [realShiftedEdge,jacobi.Bessel.edgeValue,add_zero]

end
end jacobi.EdgeResolvent
