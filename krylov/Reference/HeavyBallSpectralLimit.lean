import krylov.Reference.HeavyBallWindow
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), genuine small-coupling spectral family.
Use: keep the actual finite matrices, their strict spectral domains and real
inverse Schur endpoint functions in the sharp limiting argument.
Source: the proved genuine heavy-ball Jacobi family, its spectral window,
and standard finite-dimensional smooth inversion at a positive determinant.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator

/-- The original finite heavy-ball matrix is smooth in its real coupling.
Use: its true shifted leading inverses vary continuously at zero coupling.
Article: main_krylov, s5:fibre(b).
Proof: its actual entries are fixed polynomial functions of the coupling;
assemble them using the existing spectral-matrix coordinate equivalence. -/
theorem heavyBall_matrix_contDiffAt (d q : ℝ) (N : ℕ) {r : WithTop ℕ∞} :
    ContDiffAt ℝ r (fun t : ℝ => heavyBallMatrix d t N) q := by
  apply contDiff_spectral_matrix
  intro i j
  dsimp only [heavyBallMatrix]
  split_ifs <;> fun_prop

/-- At zero coupling the actual heavy-ball matrix is the scalar pivot matrix.
Use: the limiting leading shifted determinants are positive, not assumed.
Article: main_krylov, s5:fibre(b).
Proof: evaluate the true diagonal and adjacent entry formulas at zero. -/
theorem heavyBall_matrix_zero (d : ℝ) (N : ℕ) :
    heavyBallMatrix d 0 N=d • 1 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [heavyBallMatrix]
  · simp [heavyBallMatrix,hij]

/-- Every sufficiently small positive real coupling gives genuine strictly
interior finite heavy-ball spectra, simultaneously in every finite dimension.
Use: the limiting family stays in the actual original spectral prior.
Article: main_krylov, s5:fibre(b).
Proof: the printed heavy-ball squared window is strictly inside the given
band near zero. Its true eigenvalue bounds then prove both positive shifts. -/
theorem heavyBall_eventually_strict_band (d mu upper : ℝ)
    (hd : 0 < d) (hlo : mu < d) (hhi : d < upper) :
    ∀ᶠ q : ℝ in nhds 0,0 < q → ∀ N : ℕ,
      (heavyBallMatrix d q N-mu • 1).PosDef ∧
        (upper • 1-heavyBallMatrix d q N).PosDef := by
  have hl : ContinuousAt (fun q : ℝ => d*(1-q)^2) 0 := by fun_prop
  have hh : ContinuousAt (fun q : ℝ => d*(1+q)^2) 0 := by fun_prop
  have heL : ∀ᶠ q : ℝ in nhds 0,mu < d*(1-q)^2 :=
    hl.eventually (Ioi_mem_nhds (by simpa using hlo))
  have heH : ∀ᶠ q : ℝ in nhds 0,d*(1+q)^2 < upper :=
    hh.eventually (Iio_mem_nhds (by simpa using hhi))
  filter_upwards [heL,heH,Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with q hL hH hq1
  intro hq N
  have hw := heavyBall_spectral_window d q hd hq hq1.le N
  constructor
  · exact (positive_lower_shift_iff _ (heavyBallMatrix_posDef d q hd N).1 mu).mpr
      (fun i => hL.trans_le (hw i).1)
  · exact (positive_upper_shift_iff _ (heavyBallMatrix_posDef d q hd N).1 upper).mpr
      (fun i => (hw i).2.trans_lt hH)

/-- The literal final-diagonal Schur lower endpoint for this real family.
Use: identify actual observed physical endpoints before taking the limit.
Article: main_krylov, s5:fibre(b).
Source: scalar block Schur complement, with the actual last edge squared. -/
def heavyBallLowerEndpoint (d mu : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  mu+(d*q)^2*((heavyBallMatrix d q (n+1)-mu • 1)⁻¹) (Fin.last n) (Fin.last n)

/-- The literal final-diagonal Schur upper endpoint for this real family.
Use: retain the actual last edge and true shifted inverse.
Article: main_krylov, s5:fibre(b).
Source: the genuine upper shifted scalar Schur complement. -/
def heavyBallUpperEndpoint (d upper : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  upper-(d*q)^2*((upper • 1-heavyBallMatrix d q (n+1))⁻¹) (Fin.last n) (Fin.last n)

/-- The actual family Schur endpoints tend to the original prior endpoints.
Use: the sharp ratio limit uses genuine inverse expressions with proved
domains, rather than arbitrary abstract endpoints.
Article: main_krylov, s5:fibre(b).
Proof: the leading shifts at zero are positive scalar matrices. Smooth real
matrix inversion there and the vanishing squared edge give both limits. -/
theorem heavyBall_endpoint_limits (d mu upper : ℝ) (hlo : mu < d) (hhi : d < upper)
    (n : ℕ) :
    Filter.Tendsto (heavyBallLowerEndpoint d mu n) (nhds 0) (nhds mu) ∧
      Filter.Tendsto (heavyBallUpperEndpoint d upper n) (nhds 0) (nhds upper) := by
  have hM : ContDiffAt ℝ 1 (fun q : ℝ => heavyBallMatrix d q (n+1)) 0 :=
    heavyBall_matrix_contDiffAt d 0 (n+1)
  have hl : (heavyBallMatrix d 0 (n+1)-mu • 1).PosDef := by
    rw [heavyBall_matrix_zero,← sub_smul]
    exact Matrix.PosDef.one.smul (sub_pos.mpr hlo)
  have hh : (upper • 1-heavyBallMatrix d 0 (n+1)).PosDef := by
    rw [heavyBall_matrix_zero,← sub_smul]
    exact Matrix.PosDef.one.smul (sub_pos.mpr hhi)
  have hli := (contDiff_spectral_inverse (fun q : ℝ => heavyBallMatrix d q (n+1)-mu • 1)
    0 (hM.sub contDiffAt_const) ((Matrix.isUnit_iff_isUnit_det _).mp hl.isUnit)).continuousAt
  have hhi' := (contDiff_spectral_inverse (fun q : ℝ => upper • 1-heavyBallMatrix d q (n+1))
    0 (contDiffAt_const.sub hM) ((Matrix.isUnit_iff_isUnit_det _).mp hh.isUnit)).continuousAt
  have heval : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M (Fin.last n) (Fin.last n)) :=
    (continuous_apply (Fin.last n,Fin.last n)).comp (matrixEntryEquiv (n+1) (n+1)).continuous
  have hlentry := heval.continuousAt.comp hli
  have hhentry := heval.continuousAt.comp hhi'
  have hlc : ContinuousAt (heavyBallLowerEndpoint d mu n) 0 :=
    continuousAt_const.add ((continuousAt_const.mul continuousAt_id).pow 2 |>.mul hlentry)
  have hhc : ContinuousAt (heavyBallUpperEndpoint d upper n) 0 :=
    continuousAt_const.sub ((continuousAt_const.mul continuousAt_id).pow 2 |>.mul hhentry)
  constructor
  · simpa only [heavyBallLowerEndpoint,mul_zero,zero_pow (by norm_num : 2≠0),zero_mul,add_zero]
      using hlc.tendsto
  · simpa only [heavyBallUpperEndpoint,mul_zero,zero_pow (by norm_num : 2≠0),zero_mul,sub_zero]
      using hhc.tendsto

/-- The ratio of the genuine family endpoint pivot gaps.
Use: the actual physical dictionary identifies this function with the
original last-CG-step information ratio at each positive admissible coupling.
Article: main_krylov, s5:fibre(b).
Source: the actual family Schur threshold is d times the coupling squared. -/
def heavyBallFibreRatio (d mu upper : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  (heavyBallUpperEndpoint d upper n q-d*q^2)/(heavyBallLowerEndpoint d mu n q-d*q^2)

/-- The literal real-family pivot-gap ratio tends to the full prior ratio.
Use: establish sharpness after identifying these quantities with the actual
physical measured information fibre.
Article: main_krylov, s5:fibre(b), r tends to kappa.
Proof: both true inverse Schur endpoints have proved limits, the actual
threshold tends to zero, and the limiting lower pivot is strictly positive. -/
theorem heavyBall_fibre_ratio_limit (d mu upper : ℝ) (hmu : 0 < mu)
    (hlo : mu < d) (hhi : d < upper) (n : ℕ) :
    Filter.Tendsto (heavyBallFibreRatio d mu upper n) (nhds 0) (nhds (upper/mu)) := by
  obtain ⟨hl,hh⟩ := heavyBall_endpoint_limits d mu upper hlo hhi n
  have hs : Filter.Tendsto (fun q : ℝ => d*q^2) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun q : ℝ => d*q^2) 0 := by fun_prop
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero] using hc.tendsto
  have h := (hh.sub hs).div (hl.sub hs) (by simpa using hmu.ne')
  change Filter.Tendsto (fun q => (heavyBallUpperEndpoint d upper n q-d*q^2)/
    (heavyBallLowerEndpoint d mu n q-d*q^2)) (nhds 0) (nhds ((upper-0)/(mu-0))) at h
  change Filter.Tendsto (fun q => (heavyBallUpperEndpoint d upper n q-d*q^2)/
    (heavyBallLowerEndpoint d mu n q-d*q^2)) (nhds 0) (nhds (upper/mu))
  simpa only [sub_zero] using h

end
end krylov.Reference
