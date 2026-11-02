import krylov.LotkaVolterra.GlobalGraphRegularity
import krylov.LotkaVolterra.Barrier

/-!
Article: main_krylov, thm:limit, the coarse half-gamma constant.
Use: an exact rational polynomial barrier gives enough accuracy for the
retained kappa>=1600 Chebyshev comparison; no high-precision digits are used.
Source: the concrete LV graph equation and a rational Bernstein positivity
identity checked by Lean's ring normalization.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- A rational degree-seven upper barrier on the half-gamma lower branch. -/
def halfCoarseBarrier (U : ℝ) : ℝ := 3 - (4 - U) ^ 1 * (87 / 250) - (4 - U) ^ 2 * (12327 / 1000000) - (4 - U) ^ 3 * (1793 / 1250000) - (4 - U) ^ 4 * (10713 / 50000000) - (4 - U) ^ 5 * (36187 / 1000000000) - (4 - U) ^ 6 * (6581 / 1000000000) - (4 - U) ^ 7 * (629 / 500000000)

/-- Its literal polynomial derivative with respect to the graph variable. -/
def halfCoarseBarrierDerivative (U : ℝ) : ℝ := (4 - U) ^ 0 * (87 / 250) + (4 - U) ^ 1 * (12327 / 500000) + (4 - U) ^ 2 * (5379 / 1250000) + (4 - U) ^ 3 * (10713 / 12500000) + (4 - U) ^ 4 * (36187 / 200000000) + (4 - U) ^ 5 * (19743 / 500000000) + (4 - U) ^ 6 * (4403 / 500000000)

/-- The barrier's derivative is obtained by ordinary polynomial calculus. -/
theorem halfCoarseBarrier_hasDerivAt (U : ℝ) :
    HasDerivAt halfCoarseBarrier (halfCoarseBarrierDerivative U) U := by
  have hv := (hasDerivAt_id U).const_sub (4 : ℝ)
  have h1 := (hasDerivAt_const U (3 : ℝ)).sub ((hv.pow 1).mul_const (87 / 250))
  have h2 := h1.sub ((hv.pow 2).mul_const (12327 / 1000000))
  have h3 := h2.sub ((hv.pow 3).mul_const (1793 / 1250000))
  have h4 := h3.sub ((hv.pow 4).mul_const (10713 / 50000000))
  have h5 := h4.sub ((hv.pow 5).mul_const (36187 / 1000000000))
  have h6 := h5.sub ((hv.pow 6).mul_const (6581 / 1000000000))
  have h7 := h6.sub ((hv.pow 7).mul_const (629 / 500000000))
  convert h7 using 1
  · rfl
  · norm_num [halfCoarseBarrierDerivative]
    ring


/-- The barrier agrees with the actual saddle value. -/
@[simp] theorem halfCoarseBarrier_four : halfCoarseBarrier 4 = 3 := by norm_num [halfCoarseBarrier]

/-- Its initial value is a coarse rational upper enclosure for s(1). -/
@[simp] theorem halfCoarseBarrier_one : halfCoarseBarrier 1 = 221578863 / 125000000 := by norm_num [halfCoarseBarrier]

/-- The exact LV residual is strictly negative below the saddle.  The
certificate is an explicit sum of nonnegative Bernstein basis functions. -/
theorem halfCoarseBarrier_residual {U : ℝ} (hU : U ∈ Icc (1 : ℝ) 4) (hne : U < 4) :
    U * halfCoarseBarrierDerivative U * (halfCoarseBarrier U + 1 - U) -
      2 * halfCoarseBarrier U * (halfCoarseBarrier U - 1 - U / 2) < 0 := by
  let v := 4 - U
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have h3 : 0 ≤ 3 - v := by dsimp only [v]; linarith [hU.1]
  have hp : 0 < v := by dsimp only [v]; linarith
  let P : ℝ :=
    (13 / 49822593750) * v ^ 0 * (3 - v) ^ 13 +
    (169333 / 49822593750000) * v ^ 1 * (3 - v) ^ 12 +
    (1357318487 / 66430125000000000) * v ^ 2 * (3 - v) ^ 11 +
    (2991897053 / 39858075000000000) * v ^ 3 * (3 - v) ^ 10 +
    (4683774977 / 24911296875000000) * v ^ 4 * (3 - v) ^ 9 +
    (15016146749527 / 44286750000000000000) * v ^ 5 * (3 - v) ^ 8 +
    (1203496229067143 / 2657205000000000000000) * v ^ 6 * (3 - v) ^ 7 +
    (6144169021014787 / 13286025000000000000000) * v ^ 7 * (3 - v) ^ 6 +
    (108826529938207 / 276792187500000000000) * v ^ 8 * (3 - v) ^ 5 +
    (510607421584661843 / 1594323000000000000000000) * v ^ 9 * (3 - v) ^ 4 +
    (398417496330152939 / 1594323000000000000000000) * v ^ 10 * (3 - v) ^ 3 +
    (80249808813861769 / 531441000000000000000000) * v ^ 11 * (3 - v) ^ 2 +
    (88411962193983719 / 1594323000000000000000000) * v ^ 12 * (3 - v) ^ 1 +
    (1771960422822541 / 199290375000000000000000) * v ^ 13 * (3 - v) ^ 0
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have he : U * halfCoarseBarrierDerivative U * (halfCoarseBarrier U + 1 - U) -
      2 * halfCoarseBarrier U * (halfCoarseBarrier U - 1 - U / 2) + v / 250 = -v * P := by
    dsimp only [halfCoarseBarrier, halfCoarseBarrierDerivative, P, v]
    ring
  nlinarith [mul_nonneg hv hP]

end
end krylov.LotkaVolterra
