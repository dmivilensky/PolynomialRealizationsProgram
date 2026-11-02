import jacobi.Analytic.ReferenceNormFactors

/-!
Article: jacobi, Lemma C.1.
The two genuine original-index correction factors tend uniformly to one
on bounded positive-real-part order sets. A direct three-factor estimate
then transfers the actual uniform Euler Gamma limit to the printed norm.
Use: ReferenceNormAsymptotic discharges the compact-uniform leading coefficient.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true power correction differs from one by an explicit uniform inverse-index bound for every bounded original complex order.
Use: the actual normalized reference norm asymptotic controls its complex phase uniformly, not just its absolute magnitude.
Article: jacobi, Lemma C.1.
Proof: log(1+1/n) lies between zero and 1/n. Its actual complex exponent has norm at most 2*B/n<=1, so the community exponential remainder estimate bounds the genuine deviation by 4*B/n. -/
theorem normPowerFactor_error {g:ℂ} {B:ℝ} (hB:‖g‖≤B) {n:ℕ} (hn:0<n)
    (hlarge:2*B≤(n:ℝ)) : ‖normPowerFactor g n-1‖≤4*B/(n:ℝ) := by
  -- The positive real logarithm fixes the complex-power branch of the actual correction.
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hB0:0≤B:=(norm_nonneg g).trans hB
  have hx:0<1+1/(n:ℝ):=by positivity
  have hl0:0≤Real.log (1+1/(n:ℝ)):=Real.log_nonneg (by linarith [one_div_pos.mpr hnR])
  have hl:Real.log (1+1/(n:ℝ))≤1/(n:ℝ):=by
    have h:=Real.log_le_sub_one_of_pos hx
    linarith
  have hw:‖2*g*(Real.log (1+1/(n:ℝ)):ℂ)‖≤2*B/(n:ℝ):=by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl0]
    norm_num only [Complex.norm_ofNat]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hl hl0
      (mul_nonneg (by norm_num) hB0)).trans_eq (by ring)
  have hw1:‖2*g*(Real.log (1+1/(n:ℝ)):ℂ)‖≤1:=hw.trans ((div_le_one hnR).mpr hlarge)
  exact (Complex.norm_exp_sub_one_le hw1).trans
    ((mul_le_mul_of_nonneg_left hw (by norm_num)).trans_eq (by ring))

/-- A quantitative error bound for the three genuine complex factors in the exact normalized reference norm.
Use: ReferenceNormAsymptotic combines the actual Euler factor and the two proven elementary corrections with one vanishing scalar bound.
Article: jacobi, Lemma C.1.
Source: the triangle inequality and multiplicativity of the complex norm.
Proof: expand a*q*p-1 as (a-1)*q*p+(q-1)*p+(p-1). Bounds on the last two deviations give bounds 1+f and 1+h for their actual norms. -/
theorem norm_three_factor_error {a q p:ℂ} {e f h:ℝ}
    (ha:‖a-1‖≤e) (hq:‖q-1‖≤f) (hp:‖p-1‖≤h) :
    ‖a*q*p-1‖≤e*(1+f)*(1+h)+f*(1+h)+h := by
  -- The identity retains the actual complex factors, so the estimate also controls phase error.
  have he:0≤e:=(norm_nonneg _).trans ha
  have hf:0≤f:=(norm_nonneg _).trans hq
  have hh:0≤h:=(norm_nonneg _).trans hp
  have hqn:‖q‖≤1+f:=by
    have ht:=norm_add_le (q-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at ht
    linarith
  have hpn:‖p‖≤1+h:=by
    have ht:=norm_add_le (p-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at ht
    linarith
  rw [show a*q*p-1=(a-1)*q*p+(q-1)*p+(p-1) by ring]
  calc
    _≤‖(a-1)*q*p‖+‖(q-1)*p‖+‖p-1‖:=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤e*(1+f)*(1+h)+f*(1+h)+h:=by
      simp only [norm_mul]
      gcongr

end
end jacobi.ComplexReference
