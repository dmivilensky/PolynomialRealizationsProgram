import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: main_krylov, apG:restart, exact scalar conclusion.
Use: retain both printed restart constants after the actual geometric
energy estimate is divided by the true lower spectral endpoint.
Source: elementary positive quadratic-root bounds and sqrt(x y) <= (x+y)/2.
-/
namespace krylov.Correction
noncomputable section

/-- A nonnegative scalar satisfying the energy quadratic is bounded by
its positive linear coefficient plus the square root of its allowance.
Article: main_krylov, apG:restart, quadratic-root step. -/
theorem restart_quadratic_root {z p q : ℝ} (hp : 0≤p) (hq : 0≤q)
    (h : z^2≤p*z+q) : z≤p+Real.sqrt q := by
  by_contra hn
  have ht : p+Real.sqrt q<z := lt_of_not_ge hn
  have hs := Real.sq_sqrt hq
  nlinarith [Real.sqrt_nonneg q,mul_nonneg hp (sub_nonneg.mpr (le_of_lt ht))]

/-- The exact source non-descent constant follows from its normalized
true energy inequality. Article: main_krylov, apG:restart(a). -/
theorem sharp_nondescent_scalar {a z r g : ℝ} (ha : 0≤a) (hr : 1≤r)
    (hg : g≤a+z) (henergy : z^2≤(r+1/4)*a*z+a^2/4) :
    g≤2*(1+r)*a := by
  have hh := restart_quadratic_root (by positivity : 0≤(r+1/4)*a)
    (by positivity : 0≤a^2/4) henergy
  have hs : Real.sqrt (a^2/4)=a/2 := by
    rw [Real.sqrt_div (sq_nonneg a),Real.sqrt_sq ha]
    norm_num
  rw [hs] at hh
  nlinarith [mul_nonneg ha (by linarith : 0≤r)]

/-- The exact source short-step constant, with the canonical displacement
X, follows from the original normalized energy inequality.
Article: main_krylov, apG:restart(b), canonical-norm wording. -/
theorem sharp_short_step_scalar {a z r kappa X g : ℝ} (ha : 0≤a)
    (hX : 0≤X) (hr : 1≤r) (hk : r^2=kappa) (hg : g≤a+z)
    (henergy : z^2≤((9/4)*kappa*X+(r+1/4)*a)*z+(9/4)*kappa*X*a+a^2/4) :
    g≤4*kappa*(a+X) := by
  have hr0 : 0≤r := by linarith
  have hk1 : 1≤kappa := by nlinarith
  have hrk : r≤kappa := by nlinarith
  let q := (9/4)*kappa*X*a+a^2/4
  have hq : 0≤q := by dsimp only [q]; positivity
  have hroot := restart_quadratic_root (by positivity : 0≤(9/4)*kappa*X+(r+1/4)*a) hq (by simpa only [q,add_assoc] using henergy)
  have hs : Real.sqrt q≤(3/4)*r*(X+a)+a/2 := by
    have hR : 0≤(3/4)*r*(X+a)+a/2 := by positivity
    apply Real.sqrt_le_iff.mpr
    refine ⟨hR,?_⟩
    apply sub_nonneg.mp
    have he : ((3/4)*r*(X+a)+a/2)^2-q=
        (9/16)*r^2*(X-a)^2+(3/4)*r*(X+a)*a := by
      dsimp only [q]
      rw [←hk]
      ring
    rw [he]
    positivity
  have hcoeff : (7/4)*r+7/4≤4*kappa := by nlinarith
  have hXbound := mul_le_mul_of_nonneg_right hrk hX
  have habound := mul_le_mul_of_nonneg_right hcoeff ha
  nlinarith

/-- The printed Euclidean-norm wording of the short-step estimate fails
already for a scalar quadratic with an empty old window. At H*=25 I,
x=1, g=25, d=-25 and alpha=1/25, the canonical gradient norm is 5 while
the printed right-hand side is 4. Article: apG:restart(b), source discrepancy. -/
theorem physical_norm_short_step_counterexample :
    let H : ℝ := 25
    let g := H
    let d := -g
    let alpha := 1/H
    (-g)*d=alpha*(d*H*d) ∧ alpha>0 ∧ g*d<0 ∧
      4*(alpha*abs d) < abs g/Real.sqrt H := by
  norm_num

end
end krylov.Correction
