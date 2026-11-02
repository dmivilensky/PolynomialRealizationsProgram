import chebyshev1.SineJacobi.EllipticDescent
import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean

/-!
Article: main_krylov, apC:lem:poisson, the elliptic-integral reformulation.
Use: prove the genuine complete elliptic integral is invariant under the
arithmetic-geometric step in homogeneous coordinates. This reuses the actual
Landen integral substitution already formalized for chebyshev1.
Source: NIST DLMF 19.8, especially https://dlmf.nist.gov/19.8.E4 and E5.
-/

namespace krylov.Design
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- The homogeneous form of the genuine Legendre complete elliptic integral.
Article: main_krylov, apC:lem:poisson, the elliptic K reformulation.
Its K is the original integral, never a series defined to force the desired identity. -/
def gaussIntegral (a b : ℝ) : ℝ := ellipticK (sqrt (1 - (b / a) ^ 2)) / a

/-- The genuine homogeneous complete integral is invariant under one arithmetic-geometric step.
Article: main_krylov, apC:lem:poisson.
Proof: identify the actual descending modulus and reuse the previously proved
Landen change of variables for the original elliptic integral. -/
theorem gaussIntegral_agm_step {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    gaussIntegral a b = gaussIntegral ((a + b) / 2) (sqrt (a * b)) := by
  let x := 1 - (b / a) ^ 2
  let q := (a - b) / (a + b)
  have hsum : 0 < a + b := add_pos ha hb
  have hr : 0 < b / a := div_pos hb ha
  have hr1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hx : x ∈ Ico (0 : ℝ) 1 := by
    dsimp [x]
    exact ⟨by nlinarith, by nlinarith⟩
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hba) hsum.le
  have hq1 : q < 1 := (div_lt_one hsum).mpr (by linarith)
  have hdesc : descendingModulus x = q := by
    have hs : sqrt (1 - x) = b / a := by
      rw [show 1 - x = (b / a) ^ 2 by dsimp [x]; ring, Real.sqrt_sq hr.le]
    unfold descendingModulus
    rw [hs]
    dsimp [q]
    field_simp [ha.ne', hsum.ne']
  have hk := ellipticK_landen hq0 hq1
  have hid := descendingModulus_identity hx
  rw [hdesc] at hid
  rw [hid] at hk
  have harg : 1 - (sqrt (a * b) / ((a + b) / 2)) ^ 2 = q ^ 2 := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg ha.le hb.le)]
    dsimp [q]
    field_simp [hsum.ne']
    ring
  unfold gaussIntegral
  rw [harg, Real.sqrt_sq hq0]
  change ellipticK (sqrt x) / a = ellipticK q / ((a + b) / 2)
  rw [hk]
  dsimp [q]
  field_simp [ha.ne', hsum.ne']
  ring

/-- Actual convergence of the two AGM coordinates evaluates the genuine homogeneous integral.
Article: main_krylov, apC:lem:poisson, the Gauss integral representation. -/
theorem gaussIntegral_tendsto {α : Type*} {l : Filter α} {a b : α → ℝ} {c : ℝ}
    (ha : Tendsto a l (𝓝 c)) (hb : Tendsto b l (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun t => gaussIntegral (a t) (b t)) l (𝓝 (π / (2 * c))) := by
  have hr : Tendsto (fun t => b t / a t) l (𝓝 1) := by
    simpa only [div_self hc.ne'] using! hb.div ha hc.ne'
  have hx : Tendsto (fun t => 1 - (b t / a t) ^ 2) l (𝓝 0) := by
    simpa only [one_pow, sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hr.pow 2)
  have hs : Tendsto (fun t => sqrt (1 - (b t / a t) ^ 2)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using! Real.continuous_sqrt.continuousAt.tendsto.comp hx
  have hk := (ellipticK_continuousAt (k := 0) (by norm_num)).tendsto.comp hs
  have h := hk.div ha hc.ne'
  simpa only [gaussIntegral, ellipticK_zero, div_div] using! h

end
end krylov.Design
