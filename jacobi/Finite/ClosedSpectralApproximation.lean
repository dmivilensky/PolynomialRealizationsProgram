import jacobi.Finite.ClosedApproximation
import jacobi.Finite.MatrixSpectrumContinuity
import jacobi.Packing.Spectrum

/-!
Simultaneous energy and l1 spectral approximation of every closed-fibre chain.
Shrinking gives actual strictly contractive Jacobi matrices. The proved
matrix-inverse limit controls energy, and finite positive spectral
stability controls all sorted eigenvalues together, including multiplicities.
Use: ClosedTransfer selects these actual approximants at a vanishing
tolerance before invoking the existing all-block packing theorem.
Article: jacobi, Lemma 5.2.
Article role: continuity and contractive approximation in the closed-fibre transfer proof.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum Matrix Real Filter Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Positive normalized Green matrices only need the upper endpoint
pencil. The root minus one is allowed.
Article: jacobi, Lemma 5.2.
-/
theorem normalizedGreen_posSemidef_of_posDef {N : ℕ} {J : Jacobi N}
    (hJ : (1-J.matrix).PosDef) : J.normalizedGreen.PosSemidef :=
  hJ.inv.posSemidef.smul (by positivity)

/-- The full ordered, zero-padded spectrum for a chain whose endpoint
pencil is positive. This extends the contractive packing spectrum definition.
Article: jacobi, Lemma 5.2.
-/
def closedSpectrum {N : ℕ} (J : Jacobi N) (hJ : (1-J.matrix).PosDef) : ℕ → ℝ :=
  (matrixSpectralData J.normalizedGreen (normalizedGreen_posSemidef_of_posDef hJ)).eigenvalue

/-- Both definitions extract the same actual normalized Green spectrum
whenever the original packing's stronger contractivity condition holds.
Article: jacobi, Lemma 5.2.
-/
theorem finiteEigenvalue_eq_closedSpectrum {N : ℕ} (J : Jacobi N)
    (hc : opNorm J.matrix<1) (hJ : (1-J.matrix).PosDef) :
    Packing.finiteEigenvalue J hc=closedSpectrum J hJ := rfl

/-- Matrix convergence also holds after the fixed squared-dimension scaling.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_normalizedGreen_limit {N : ℕ} (J : Jacobi N)
    (hJ : (1-J.matrix).PosDef) :
    Tendsto (fun e : ℝ => (closedApproximation J e).normalizedGreen) (𝓝 0)
      (𝓝 J.normalizedGreen) :=
  (closedApproximation_green_limit J hJ).const_smul ((N:ℝ)^2)⁻¹

/-- The l1 matrix error controlling the entire finite spectrum tends to zero.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_spectral_error_limit {N : ℕ} (J : Jacobi N)
    (hJ : (1-J.matrix).PosDef) :
    Tendsto (fun e : ℝ => matrixEntryDistance
      (closedApproximation J e).normalizedGreen J.normalizedGreen) (𝓝 0) (𝓝 0) :=
  matrixEntryDistance_limit (closedApproximation_normalizedGreen_limit J hJ)

/-- Every closed-fibre member admits an actual strictly contractive
approximation with arbitrarily small real energy error and full sorted
spectral l1 error. All approximation and continuity obligations are proved.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.exists_spectral_approximation {N : ℕ} (S : ClosedNodes N)
    {J : Jacobi N} (hJ : InClosedFiber J S.polynomial) {d : ℝ} (hd : 0<d) :
    ∃ K : Jacobi N,∃ hc : opNorm K.matrix<1,
      |K.energy-J.energy|<d ∧
        (∑' j,|Packing.finiteEigenvalue K hc j-closedSpectrum J (S.endpoint_posDef hJ) j|)<d := by
  have hp := S.endpoint_posDef hJ
  have hE := ((closedApproximation_energy_limit J hp).sub
    (tendsto_const_nhds (x := J.energy))).abs
  have hE' : ∀ᶠ e : ℝ in 𝓝 0,|(closedApproximation J e).energy-J.energy|<d := by
    exact hE.eventually (Iio_mem_nhds (by simpa only [sub_self,abs_zero] using hd))
  have hM : ∀ᶠ e : ℝ in 𝓝 0,matrixEntryDistance
      (closedApproximation J e).normalizedGreen J.normalizedGreen<d :=
    (closedApproximation_spectral_error_limit J hp).eventually (Iio_mem_nhds hd)
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp (hE'.and hM)
  let e : ℝ := min (r/2) (1/2)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have he1 : e<1 := (min_le_right _ _).trans_lt (by norm_num)
  have her : dist e 0<r := by
    rw [Real.dist_eq,sub_zero,abs_of_pos he]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hh := hbound her
  let K := closedApproximation J e
  have hc : opNorm K.matrix<1 := S.approximation_contractive hJ he he1
  refine ⟨K,hc,hh.1,?_⟩
  have hspec := matrixSpectrum_distance_le K.normalizedGreen J.normalizedGreen
    (Packing.normalizedGreen_positive K hc) (normalizedGreen_posSemidef_of_posDef hp)
  exact hspec.trans_lt hh.2

end
end jacobi.Finite
