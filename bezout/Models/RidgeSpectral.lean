import bezout.Models.RidgeAverage
import bezout.Probability.CovarianceSpectral
import bezout.Probability.CovarianceIsotropic
import bezout.History.Transport

/-!
Article: bezout, Equations `eq:experiment-ridge` and `eq:experiment-mse`.
Use: the actual rank-one ridge Hessian along any unit vector admits genuine
orthonormal coordinates with exactly one exceptional eigenvalue. Its physical
MSE has the symbolic bulk/direction energy split, independently of orientation.
Proof: extend the unit vector to an orthonormal basis, intertwine the actual
causal execution, and identify isotropic covariance in those constructed coordinates.
-/

namespace bezout.Models.Ridge
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every prescribed unit direction belongs to a genuine orthonormal basis. -/
theorem exists_basis_with_unit (v : E) (hv : ‖v‖=1) :
    ∃ (j0 : Fin (Module.finrank ℝ E)) (B : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E),
      B j0=v := by
  classical
  have hvne : v≠0 := by intro h; simp [h] at hv
  let _ : Nontrivial E := ⟨⟨v,0,hvne⟩⟩
  let j0 : Fin (Module.finrank ℝ E) := ⟨0,Module.finrank_pos⟩
  have hon : Orthonormal ℝ (({j0} : Set (Fin (Module.finrank ℝ E))).domRestrict (fun _ => v)) := by
    rw [orthonormal_subsingleton_iff]
    intro _
    exact hv
  obtain ⟨B,hB⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨j0,B,hB j0 (by simp)⟩

omit [FiniteDimensional ℝ E] in
/-- An orthonormal basis containing v diagonalizes its literal rank-one Hessian. -/
theorem spectralMap_coordinates {J : Type*} [Fintype J] [DecidableEq J]
    (B : OrthonormalBasis J ℝ E) (j0 : J) (v : E) (hb : B j0=v)
    (mu L : ℝ) (x : E) (j : J) :
    B.repr (spectralMap v mu L x) j=
      bezout.Probability.twoLevelEigenvalues j0 mu L j*B.repr x j := by
  rw [spectralMap_apply,map_add,map_smul,map_smul]
  have hv : B.repr v=EuclideanSpace.single j0 1 := by rw [← hb,B.repr_self]
  rw [hv]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply,
    bezout.Probability.twoLevelEigenvalues]
  by_cases hj : j=j0
  · subst j
    simp only [ite_true,mul_one]
    rw [B.repr_apply_apply, hb]
    ring
  · simp only [hj,ite_false,mul_zero,add_zero]

omit [FiniteDimensional ℝ E] in
/-- Full noisy physical execution, not only nominal polynomial action, commutes
with the constructed rank-one spectral coordinates. -/
theorem run_coordinates {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (h : bezout.History N) (B : OrthonormalBasis J ℝ E) (j0 : J) (v : E)
    (hb : B j0=v) (mu L : ℝ) (initial : E) (noise : Fin N → E) :
    B.repr ((h.run (spectralMap v mu L).toLinearMap initial noise).output)=
      (h.run (bezout.History.matrixEnd (Matrix.diagonal
        (bezout.Probability.twoLevelEigenvalues j0 mu L))) (B.repr initial)
        (fun s => B.repr (noise s))).output := by
  have he := h.oracleOutput_map B.repr.toLinearEquiv.toLinearMap initial
    (fun s x => spectralMap v mu L x+noise s)
    (fun s y => bezout.History.matrixEnd
      (Matrix.diagonal (bezout.Probability.twoLevelEigenvalues j0 mu L)) y+B.repr (noise s)) (by
      intro s x
      rw [map_add]
      congr 1
      ext j
      change (bezout.History.matrixEnd (Matrix.diagonal
        (bezout.Probability.twoLevelEigenvalues j0 mu L)) (B.repr x)) j=
          B.repr (spectralMap v mu L x) j
      rw [spectralMap_coordinates B j0 v hb mu L x j]
      change (Matrix.diagonal (bezout.Probability.twoLevelEigenvalues j0 mu L)).mulVec (B.repr x).ofLp j=_
      simp [Matrix.mulVec,dotProduct,Matrix.diagonal])
  rw [bezout.History.oracleOutput_linear] at he
  have ho := h.oracleOutput_linear (spectralMap v mu L).toLinearMap initial noise
  change h.oracleOutput initial (fun s x => spectralMap v mu L x+noise s)=
    (h.run (spectralMap v mu L).toLinearMap initial noise).output at ho
  rw [ho] at he
  exact he.symm

/-- The symbolic multiplicity split is valid for every unit direction, including
arbitrary orientation relative to the original physical coordinates. Isotropy
is stated intrinsically as an actual second-moment identity, without assuming
any diagonalizing basis or any execution transfer identity. -/
theorem integral_stochasticOutput_rankOne [CompleteSpace E] {N : ℕ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (h : bezout.History N) (v : E) (hv : ‖v‖=1) (mu L variance : ℝ) (initial : E)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (hiso : ∀ s : Fin N, ∀ x y : E,
      (∫ ω, inner ℝ x (w s.val ω)*inner ℝ y (w s.val ω) ∂μ)=variance*inner ℝ x y) :
    (∫ ω, ‖h.stochasticOutput (spectralMap v mu L).toLinearMap initial w ω‖^2 ∂μ)=
      (‖initial‖^2-(inner ℝ v initial)^2)*h.terminal.eval mu^2+
      (inner ℝ v initial)^2*h.terminal.eval L^2+
      variance*((Module.finrank ℝ E-1 : ℕ)*bezout.Probability.varianceProfile h mu+
        bezout.Probability.varianceProfile h L) := by
  classical
  obtain ⟨j0,B,hB⟩ := exists_basis_with_unit v hv
  let wB : ℕ → Ω → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun s ω => B.repr (w s ω)
  have hwB : bezout.Probability.MartingaleDifferences N 𝓕 wB μ :=
    hw.map (fun _ => B.repr.toContinuousLinearEquiv.toContinuousLinearMap)
  have hcov (s : Fin N) : bezout.Probability.covarianceMatrix (wB s.val) μ=
      Matrix.diagonal (fun _ => variance) := by
    rw [bezout.Probability.covarianceMatrix_of_mean_zero _ (hwB.integral_eq_zero s.val s.isLt)]
    ext i j
    change (∫ ω, B.repr (w s.val ω) i*B.repr (w s.val ω) j ∂μ)=_
    simp only [B.repr_apply_apply]
    rw [hiso s]
    rw [orthonormal_iff_ite.mp B.orthonormal]
    simp [Matrix.diagonal]
  have he (ω : Ω) : ‖h.stochasticOutput (spectralMap v mu L).toLinearMap initial w ω‖^2=
      ‖h.stochasticOutput (bezout.History.matrixEnd (Matrix.diagonal
        (bezout.Probability.twoLevelEigenvalues j0 mu L))) (B.repr initial) wB ω‖^2 := by
    rw [← B.repr.norm_map]
    exact congrArg (fun x => ‖x‖^2) (run_coordinates h B j0 v hB mu L initial (fun s => w s.val ω))
  simp_rw [he]
  rw [h.integral_stochasticOutput_rankOne j0 mu L variance (B.repr initial) hwB hcov]
  have hcoord : B.repr initial j0=inner ℝ v initial := by rw [B.repr_apply_apply,hB]
  have hbulk : (∑ j∈Finset.univ.erase j0, (B.repr initial j)^2)=
      ‖initial‖^2-(inner ℝ v initial)^2 := by
    have hs := Finset.sum_erase_add Finset.univ (fun j => (B.repr initial j)^2) (Finset.mem_univ j0)
    have hn : (∑ j, (B.repr initial j)^2)=‖initial‖^2 := by
      have hh := congrArg (fun t : ℝ => t^2) (B.repr.norm_map initial)
      rw [EuclideanSpace.norm_sq_eq] at hh
      simpa only [Real.norm_eq_abs,sq_abs] using hh
    rw [hcoord,hn] at hs
    linarith
  rw [hbulk,hcoord]
  simp only [Fintype.card_fin]

/-- The literal coordinate-isotropic worker noise gives the orientation-free
rank-one ridge MSE; the distinguished vector is arbitrary and its basis is
constructed inside the proof. -/
theorem integral_stochasticOutput_rankOne_covariance {N : ℕ} {J Ω : Type*}
    [Fintype J] [DecidableEq J] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → EuclideanSpace ℝ J}
    (h : bezout.History N) (v : EuclideanSpace ℝ J) (hv : ‖v‖=1)
    (mu L variance : ℝ) (initial : EuclideanSpace ℝ J)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (hcov : ∀ s : Fin N, bezout.Probability.covarianceMatrix (w s.val) μ=
      variance • (1 : Matrix J J ℝ)) :
    (∫ ω, ‖h.stochasticOutput (spectralMap v mu L).toLinearMap initial w ω‖^2 ∂μ)=
      (‖initial‖^2-(inner ℝ v initial)^2)*h.terminal.eval mu^2+
      (inner ℝ v initial)^2*h.terminal.eval L^2+
      variance*((Fintype.card J-1 : ℕ)*bezout.Probability.varianceProfile h mu+
        bezout.Probability.varianceProfile h L) := by
  simpa using integral_stochasticOutput_rankOne h v hv mu L variance initial hw
    (fun s x y => bezout.Probability.covariance_isotropic_inner
      (hw.squareIntegrable s.val s.isLt) (hw.integral_eq_zero s.val s.isLt)
      variance (hcov s) x y)

end
end bezout.Models.Ridge
