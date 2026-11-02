import krylov.Design.EllipticAGMStep

/-!
Article: main_krylov, apC:lem:poisson, genuine elliptic K versus AGM.
Use: iterate the already proved integral-preserving Gauss step, then pass to
mathlib's actual arithmetic-geometric limit. This proves Gauss's integral
formula for the original complete elliptic integral before any nome identity.
Source: NIST DLMF https://dlmf.nist.gov/19.8.E4 and 19.8.E5.
-/

namespace krylov.Design
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- Both genuine AGM coordinates remain strictly positive for positive initial data.
Article: main_krylov, apC:lem:poisson, the legitimate Gauss iteration domain. -/
theorem agmCoordinates_pos {x y : NNReal} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    0 < ((NNReal.agmSequences x y n).1 : ℝ) ∧ 0 < ((NNReal.agmSequences x y n).2 : ℝ) := by
  have hzero : 0 < ((NNReal.agmSequences x y 0).1 : ℝ) := by
    simpa only [NNReal.agmSequences_zero, Real.coe_sqrt, NNReal.coe_mul] using
      Real.sqrt_pos.mpr (mul_pos (NNReal.coe_pos.mpr hx) (NNReal.coe_pos.mpr hy))
  have hm : ((NNReal.agmSequences x y 0).1 : ℝ) ≤ ((NNReal.agmSequences x y n).1 : ℝ) := by
    exact_mod_cast NNReal.agmSequences_fst_monotone (x := x) (y := y) (Nat.zero_le n)
  have hba : ((NNReal.agmSequences x y n).1 : ℝ) ≤ ((NNReal.agmSequences x y n).2 : ℝ) := by
    exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n
  exact ⟨hzero.trans_le hm, (hzero.trans_le hm).trans_le hba⟩

/-- Every actual AGM iterate retains the genuine original homogeneous integral.
Article: main_krylov, apC:lem:poisson, the iterated Gauss integral identity. -/
theorem gaussIntegral_agm_iterate {x y : NNReal} (hx : 0 < x) (hy : 0 < y) (hyx : y ≤ x) (n : ℕ) :
    gaussIntegral ((NNReal.agmSequences x y n).2 : ℝ) ((NNReal.agmSequences x y n).1 : ℝ) =
      gaussIntegral x y := by
  induction n with
  | zero =>
    simpa only [NNReal.agmSequences_zero, NNReal.coe_div, NNReal.coe_add, NNReal.coe_two,
      Real.coe_sqrt, NNReal.coe_mul] using
      (gaussIntegral_agm_step (NNReal.coe_pos.mpr hx) (NNReal.coe_pos.mpr hy)
        (NNReal.coe_le_coe.mpr hyx)).symm
  | succ n ih =>
    have hp := agmCoordinates_pos hx hy n
    have hba : ((NNReal.agmSequences x y n).1 : ℝ) ≤ ((NNReal.agmSequences x y n).2 : ℝ) := by
      exact_mod_cast NNReal.agmSequences_fst_le_snd (x := x) (y := y) n n
    have hs := gaussIntegral_agm_step hp.2 hp.1 hba
    rw [NNReal.agmSequences_succ']
    simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_two, Real.coe_sqrt,
      NNReal.coe_mul, add_comm, mul_comm] using hs.symm.trans ih

/-- Gauss's exact genuine elliptic integral representation of the arithmetic-geometric mean.
Article: main_krylov, apC:lem:poisson.
Proof: actual positive iterates preserve the original integral; both coordinates
converge to mathlib's AGM, where the complete integral is evaluated at zero. -/
theorem gaussIntegral_eq_agm {x y : NNReal} (hx : 0 < x) (hy : 0 < y) (hyx : y ≤ x) :
    gaussIntegral x y = π / (2 * (NNReal.agm x y : ℝ)) := by
  have ha : Tendsto (fun n : ℕ => ((NNReal.agmSequences x y n).2 : ℝ)) atTop
      (𝓝 (NNReal.agm x y : ℝ)) := by
    exact NNReal.continuous_coe.continuousAt.tendsto.comp NNReal.tendsto_agmSequences_snd_agm
  have hb : Tendsto (fun n : ℕ => ((NNReal.agmSequences x y n).1 : ℝ)) atTop
      (𝓝 (NNReal.agm x y : ℝ)) := by
    exact NNReal.continuous_coe.continuousAt.tendsto.comp NNReal.tendsto_agmSequences_fst_agm
  have hc : 0 < (NNReal.agm x y : ℝ) := NNReal.coe_pos.mpr (NNReal.agm_pos hx hy)
  have h := gaussIntegral_tendsto ha hb hc
  simp only [gaussIntegral_agm_iterate hx hy hyx] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- The original Legendre complete elliptic integral equals pi divided by twice the actual AGM.
Article: main_krylov, apC:lem:poisson, the genuine elliptic integral bridge.
The right-hand mean is mathlib's convergent arithmetic-geometric iteration;
the left-hand function is the existing physical interval integral. -/
theorem ellipticK_eq_agm {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) :
    ellipticK k = π / (2 * (NNReal.agm 1 (Real.toNNReal (sqrt (1 - k ^ 2))) : ℝ)) := by
  have hs : 0 < 1 - k ^ 2 := by nlinarith
  have hb : 0 < Real.toNNReal (sqrt (1 - k ^ 2)) := Real.toNNReal_pos.mpr (sqrt_pos.mpr hs)
  have hb1 : Real.toNNReal (sqrt (1 - k ^ 2)) ≤ 1 := by
    apply Real.toNNReal_le_one.mpr
    exact (sqrt_le_one).mpr (by nlinarith [sq_nonneg k])
  have h := gaussIntegral_eq_agm (x := 1) (y := Real.toNNReal (sqrt (1 - k ^ 2)))
    zero_lt_one hb hb1
  have harg : sqrt (1 - sqrt (1 - k ^ 2) ^ 2) = k := by
    rw [Real.sq_sqrt hs.le, sub_sub_cancel, Real.sqrt_sq hk]
  simpa only [gaussIntegral, NNReal.coe_one, Real.coe_toNNReal _ (sqrt_nonneg _), div_one, harg] using h

end
end krylov.Design
