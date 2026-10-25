import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The uniform first-order Taylor remainder for a phase with Lipschitz
first derivative. No global second differentiability is required. -/
noncomputable section
namespace polyak.Global.Sampling

theorem scalar_descent {f df : ℝ→ℝ} {M : ℝ}
    (hf : ∀x,HasDerivAt f (df x) x)
    (hlip : ∀x y,|df x-df y|≤M*|x-y|) (x y : ℝ) :
    f y≤f x+df x*(y-x)+M/2*(y-x)^2 := by
  let d:=y-x
  let φ:ℝ→ℝ:=fun s=>f (x+s*d)-f x-s*df x*d-M/2*s^2*d^2
  have hφ (s:ℝ) : HasDerivAt φ ((df (x+s*d)-df x)*d-M*s*d^2) s := by
    have hh:=(hf (x+s*d)).comp s (((hasDerivAt_id s).mul_const d).const_add x)
    convert ((hh.sub_const (f x)).sub (((hasDerivAt_id s).mul_const (df x)).mul_const d)).sub
      ((((hasDerivAt_id s).pow 2).const_mul (M/2)).mul_const (d^2)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hmono : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun s _=>(hφ s).continuousAt.continuousWithinAt)
      (fun s _=>(hφ s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hφ s).deriv]
    have hs0 : 0≤s:=(interior_subset hs).1
    have hd:=hlip (x+s*d) x
    simp only [add_sub_cancel_left,abs_mul,abs_of_nonneg hs0] at hd
    have hp : (df (x+s*d)-df x)*d≤|df (x+s*d)-df x| * |d|:=by
      rw [←abs_mul]
      exact le_abs_self _
    have hm:=mul_le_mul_of_nonneg_right hd (abs_nonneg d)
    have he : M*(s*|d|)*|d|=M*s*d^2 := by
      calc
        _ = M*s*(|d|^2) := by ring
        _ = _ := by rw [sq_abs]
    rw [he] at hm
    linarith
  have hh:=hmono (by simp) (by simp) (by norm_num : (0:ℝ)≤1)
  dsimp [φ] at hh
  simp only [zero_mul, add_zero, one_mul, sub_self, one_pow,
    zero_pow (by norm_num : 2≠0)] at hh
  dsimp [d] at hh
  have he : x+(y-x)=y := by ring
  rw [he] at hh
  nlinarith

theorem phase_taylor_bound {f df : ℝ→ℝ} {M : ℝ}
    (hf : ∀x,HasDerivAt f (df x) x)
    (hlip : ∀x y,|df x-df y|≤M*|x-y|) (v t : ℝ) :
    |f (v+t)-f v-df v*t|≤M*t^2/2 := by
  have hfn (x:ℝ) : HasDerivAt (fun x=>-f x) (-df x) x:=by
    convert (hf x).neg using 1
  have hLn (x y:ℝ) : |-df x- -df y|≤M*|x-y|:=by
    simpa only [neg_sub_neg,abs_sub_comm] using hlip x y
  have hu:=scalar_descent hf hlip v (v+t)
  have hl:=scalar_descent hfn hLn v (v+t)
  simp only [add_sub_cancel_left] at hu hl
  apply abs_le.mpr
  constructor <;> nlinarith

end polyak.Global.Sampling
