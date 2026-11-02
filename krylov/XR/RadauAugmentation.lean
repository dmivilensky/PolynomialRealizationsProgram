import krylov.Convergence.WindowAugmentation
import krylov.XR.LocalFrameBounds

/-!
Article: main_krylov, apG:radau-adequate, primitive augmented-frame domain.
Use: derive independence of the actual stored window plus computed new
direction from only the old least gain, true reference positivity and
measured image conjugacy. Source: exact block energy and finite
Cauchy--Schwarz. No augmented-rank or Schur-feasibility premise is added.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Convergence
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Actual image conjugacy controls the true reference cross entry by
the measured secant error, on a genuine unit direction.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_reference_cross (H : E →L[ℝ] E) (s y : Fin p → E) (d : E)
    (hd : ‖d‖=1) (epsilon : ℝ) (hy : ∀ i,‖y i-H (s i)‖≤epsilon)
    (ho : ∀ i,inner ℝ (y i) d=0) (i : Fin p) : |inner ℝ (H (s i)) d|≤epsilon := by
  have hh := norm_inner_le_norm (𝕜 := ℝ) (H (s i)-y i) d
  rw [Real.norm_eq_abs,inner_sub_left,ho i,sub_zero,hd,mul_one] at hh
  exact hh.trans (by simpa only [norm_sub_rev] using hy i)

/-- The true positive-reference energy of the actual augmented frame has
a uniform coefficient lower bound before any Schur construction.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_augmented_energy (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (d : E) (a sigma epsilon : ℝ)
    (ha : 0≤a) (hsigma : 0≤sigma) (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hd : ‖d‖=1)
    (hlower : ∀ v : E,a*‖v‖^2≤ inner ℝ v (H v))
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hy : ∀ i,‖y i-H (s i)‖≤epsilon) (ho : ∀ i,inner ℝ (y i) d=0)
    (c : Fin (p+1) → ℝ) :
    (a*sigma^2-Real.sqrt p*epsilon)*‖WithLp.toLp 2 c‖^2≤
      inner ℝ (combine (Fin.snoc s d) c) (H (combine (Fin.snoc s d) c)) := by
  let u := combine s (fun i=>c i.castSucc)
  let t := c (Fin.last p)
  let b := WithLp.toLp 2 (fun i : Fin p=>c i.castSucc)
  have hcross := combine_pairing_bound (fun i=>H (s i)) d he
    (radau_reference_cross H s y d hd epsilon hy ho) (fun i=>c i.castSucc)
  have hHu : combine (fun i=>H (s i)) (fun i=>c i.castSucc)=H u := by
    simp only [u,combine,map_sum,map_smul]
  rw [hHu] at hcross
  have hsquare : sigma^2≤1 := by nlinarith only [hsigma,hsigma₁]
  have hold : a*sigma^2*‖b‖^2≤ inner ℝ u (H u) := by
    have hh := mul_le_mul_of_nonneg_left (hgain (fun i=>c i.castSucc)) ha
    exact (by nlinarith only [hh] : a*sigma^2*‖b‖^2≤a*‖u‖^2).trans (hlower u)
  have hnew : a*sigma^2≤ inner ℝ d (H d) := by
    have hh := hlower d
    rw [hd,one_pow,mul_one] at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hsquare ha]
  have htwocross : -(Real.sqrt p*epsilon)*(t^2+‖b‖^2)≤2*t*inner ℝ (H u) d := by
    have habs : -|t| * |inner ℝ (H u) d|≤t*inner ℝ (H u) d := by
      rw [neg_mul,←abs_mul]
      exact neg_abs_le _
    have hh := mul_le_mul_of_nonneg_left hcross (abs_nonneg t)
    have hyoung : 2*|t| * ‖b‖≤t^2+‖b‖^2 := by nlinarith only [sq_nonneg (|t|-‖b‖),sq_abs t]
    have hscale := mul_le_mul_of_nonneg_left hyoung (by positivity : 0≤Real.sqrt p*epsilon)
    nlinarith only [habs,hh,hscale]
  have hpair : inner ℝ u (H d)=inner ℝ (H u) d := (hH u d).symm
  rw [combine_snoc_window,coefficient_norm_snoc_sq]
  change (a*sigma^2-Real.sqrt p*epsilon)*(‖b‖^2+t^2)≤ inner ℝ (u+t • d) (H (u+t • d))
  rw [map_add,map_smul,inner_add_left,inner_add_right,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_smul_left,real_inner_smul_right,hpair]
  have hcomm : inner ℝ d (H u)=inner ℝ (H u) d := real_inner_comm _ _
  rw [hcomm]
  have ht := mul_le_mul_of_nonneg_left hnew (sq_nonneg t)
  nlinarith only [hold,ht,htwocross]

/-- The actual augmented physical frame has a positive least-gain
squared, derived from the old-window hypothesis alone.
Article: main_krylov, apG:radau-adequate, Schur domain. -/
theorem radau_augmented_gain (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (d : E) (a b sigma epsilon : ℝ)
    (ha : 0<a) (hb : 0<b) (hsigma : 0<sigma) (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hd : ‖d‖=1)
    (hlower : ∀ v : E,a*‖v‖^2≤ inner ℝ v (H v)) (hupper : ‖H‖≤b)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hy : ∀ i,‖y i-H (s i)‖≤epsilon) (ho : ∀ i,inner ℝ (y i) d=0)
    (hsmall : Real.sqrt p*epsilon≤a*sigma^2/2) (c : Fin (p+1) → ℝ) :
    (a*sigma^2/(2*b))*‖WithLp.toLp 2 c‖^2≤‖combine (Fin.snoc s d) c‖^2 := by
  let v := combine (Fin.snoc s d) c
  have hh := radau_augmented_energy H hH s y d a sigma epsilon ha.le hsigma.le hsigma₁ he hd hlower hgain hy ho c
  have hup : inner ℝ v (H v)≤b*‖v‖^2 := by
    have hn := (H.le_opNorm v).trans (mul_le_mul_of_nonneg_right hupper (norm_nonneg v))
    nlinarith only [real_inner_le_norm v (H v),mul_le_mul_of_nonneg_left hn (norm_nonneg v)]
  have hlo : a*sigma^2/2*‖WithLp.toLp 2 c‖^2≤b*‖v‖^2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖WithLp.toLp 2 c‖)
    nlinarith only [hh,hup,hm]
  have hdiv : (a*sigma^2/2*‖WithLp.toLp 2 c‖^2)/b≤‖v‖^2 :=
    (div_le_iff₀ hb).mpr (by nlinarith only [hlo])
  convert hdiv using 1
  field_simp

end
end krylov.XR
