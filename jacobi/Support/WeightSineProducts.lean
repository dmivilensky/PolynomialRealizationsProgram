import jacobi.Support.WeightFormula
import jacobi.Support.SineProducts

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Reflecting the cosine factors in the exact probability formula expresses
its entire finite product using two of the already estimated sine products.
This gives a direct route to the global weight bounds without a separate
log-cosine estimate.
Use: weightFactor_sineProducts divides by the genuine endpoint product, and the global weight bounds reuse the same positive products for both endpoint exponents.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The actual support half-step sine products are positive throughout the full original chain.
Use: weightFactor_sineProducts divides by the genuine endpoint product, and the global weight bounds reuse the same positive products for both endpoint exponents.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: each original argument lies strictly between zero and pi. The half-step doubles the allowed original frequency, and the stated shift covers both actual choices 2*gamma_alpha and 2*gamma_beta. -/
theorem support_half_sineProduct_pos {a b s:ℝ} (ha:-1<a) (hb:-1<b) (hs:0<s)
    (hshift:s<2*(gamma a+gamma b)+1) {n m:ℕ} (hm:m≤n) :
    0<sineProduct (step a b (n+1)/2) s m := by
  -- Bound every shifted half-step angle inside (0, pi), then multiply positive sines.
  have hg := parameter_pos ha hb
  have hf := frequency_gamma a b (n+1)
  push_cast at hf
  have hn0 := Nat.cast_nonneg n (α:=ℝ)
  have hp (p:ℝ) (j:ℕ) (hj:j<m) (hp:0<p) (hps:p<2*(gamma a+gamma b)+1) :
      0<((j:ℝ)+p)*(step a b (n+1)/2) ∧ ((j:ℝ)+p)*(step a b (n+1)/2)<π := by
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    have hjn : (j:ℝ)+1≤n := by exact_mod_cast (show j+1≤n by omega)
    have hx0 : 0<((j:ℝ)+p)/2 := by linarith
    have hxN : ((j:ℝ)+p)/2< jacobi.Jacobi.frequency a b (n+1) := by linarith
    constructor
    · exact mul_pos (by linarith) (div_pos (step_pos ha hb (show 0<n+1 by omega)) (by norm_num))
    · rw [← frequency_mul_step ha hb (show 0<n+1 by omega)]
      have hh := mul_lt_mul_of_pos_right hxN (step_pos ha hb (show 0<n+1 by omega))
      nlinarith only [hh]
  exact sineProduct_pos (fun j hj => hp s j hj hs hshift)
    (fun j hj => hp 1 j hj (by norm_num) (by linarith [hg.1,hg.2.1]))

/-- The original cosine quotient is exactly a reflected positive half-step sine quotient.
Use: weightFactor_sineProducts telescopes the beta-side factors into the same sine products already controlled in Appendix C.3.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the original period gives each cosine as the sine of pi/2 minus its unchanged argument. -/
theorem weightIncrement_reflected (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    weightIncrement a b (n+1) k=
      (sin (((k:ℝ)+2*gamma a)*step a b (n+1)/2)/sin (((k:ℝ)+1)*step a b (n+1)/2))*
        (sin (((n:ℝ)-k)*step a b (n+1)/2)/
          sin (((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2)) := by
  have hper := frequency_mul_step ha hb (show 0<n+1 by omega)
  rw [frequency_gamma] at hper
  push_cast at hper
  -- Reflect the denominator as well as the numerator; both remain the exact original factors.
  have hden : sin (((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2)=
      cos (((k:ℝ)+1+gamma a-gamma b)*step a b (n+1)/2) := by
    rw [show ((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2=
      π/2-(((k:ℝ)+1+gamma a-gamma b)*step a b (n+1)/2) by nlinarith only [hper],sin_pi_div_two_sub]
  rw [hden,(weight_period_factors ha hb n k).2]
  simp only [weightIncrement,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The full original sine-cosine product equals a quotient of the two endpoint half-step sine products.
Use: weightFactor_sineProducts and supportWeight_ratio_bounds transfer the proved original sine-product power estimates to the genuine support probabilities.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: induction in the genuine spectral index telescopes the reflected beta quotient. The alpha product gains precisely its next factor; the beta product loses precisely its last factor. The positive endpoint product fixes the exact empty-product normalization. -/
theorem weightProduct_sineProducts {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    (∏j∈Finset.range k,weightIncrement a b (n+1) j)=
      sineProduct (step a b (n+1)/2) (2*gamma a) k*
        sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/
          sineProduct (step a b (n+1)/2) (2*gamma b) n := by
  -- Prove the product identity first, keeping the original angular sine outside it.
  have hg := parameter_pos ha hb
  have hP : 0<sineProduct (step a b (n+1)/2) (2*gamma b) n :=
    support_half_sineProduct_pos ha hb (by linarith [hg.2.1]) (by linarith [hg.1]) le_rfl
  have hprod (k:ℕ) (hk:k≤n) : (∏j∈Finset.range k,weightIncrement a b (n+1) j)=
      sineProduct (step a b (n+1)/2) (2*gamma a) k*
        sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/
          sineProduct (step a b (n+1)/2) (2*gamma b) n := by
    induction k with
    | zero => simp [sineProduct_zero,hP.ne']
    | succ k ih =>
      have hk' : k<n := by omega
      have hcast : ((n-(k+1):ℕ):ℝ)=(n:ℝ)-k-1 := by
        have he : ((n-(k+1):ℕ):ℝ)+(k:ℝ)+1=n := by exact_mod_cast (show n-(k+1)+k+1=n by omega)
        linarith
      have hprev : sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)=
          sineProduct (step a b (n+1)/2) (2*gamma b) (n-(k+1))*
            (sin (((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2)/
              sin (((n:ℝ)-k)*step a b (n+1)/2)) := by
        rw [show n-k=n-(k+1)+1 by omega,sineProduct_succ,hcast]
        congr 2 <;> congr 1 <;> ring
      have hf := frequency_gamma a b (n+1)
      push_cast at hf
      have hn0 := Nat.cast_nonneg n (α:=ℝ)
      have hk0 := Nat.cast_nonneg k (α:=ℝ)
      have hkn : (k:ℝ)+1≤n := by exact_mod_cast hk'
      have hs (x:ℝ) (hx:0<x) (hxN:x<2* jacobi.Jacobi.frequency a b (n+1)) :
          sin (x*step a b (n+1)/2)≠0 := by
        have hp := sin_position_pos ha hb (show 0<n+1 by omega)
          (show 0<x/2 by linarith) (show x/2< jacobi.Jacobi.frequency a b (n+1) by linarith)
        convert hp.ne' using 1
        congr 2
        ring
      have hnum := hs ((n:ℝ)-k-1+2*gamma b) (by linarith [hg.2.1]) (by linarith [hg.1])
      have hden := hs ((n:ℝ)-k) (by linarith) (by linarith [hg.1,hg.2.1])
      rw [Finset.prod_range_succ,ih (by omega),weightIncrement_reflected a b ha hb,hprev,sineProduct_succ]
      have he (x:ℝ) : x*(step a b (n+1)/2)=x*step a b (n+1)/2 := by ring
      simp_rw [he]
      let V := sineProduct (step a b (n+1)/2) (2*gamma a) k*
        (sin (((k:ℝ)+2*gamma a)*step a b (n+1)/2)/sin (((k:ℝ)+1)*step a b (n+1)/2))*
          sineProduct (step a b (n+1)/2) (2*gamma b) (n-(k+1))/
            sineProduct (step a b (n+1)/2) (2*gamma b) n
      change _=V
      calc
        _ = V*((sin (((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2)/sin (((n:ℝ)-k)*step a b (n+1)/2))*
          (sin (((n:ℝ)-k)*step a b (n+1)/2)/sin (((n:ℝ)-k-1+2*gamma b)*step a b (n+1)/2))) := by dsimp [V]; ring
        _ = V := by rw [div_mul_div_cancel₀ hden,div_self hnum,mul_one]
  exact hprod k hk

/-- The complete original support probability factor is a product of the two endpoint half-step sine products and its actual angular sine.
Use: global weight estimates apply the same already verified sine-product estimates to the actual natural and corrected spectral probabilities.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: multiply the exact preceding product identity by the genuine angular sine and reassociate its factors. -/
theorem weightFactor_sineProducts {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    weightFactor a b (n+1) k=
      sin (jacobi.Jacobi.modelAngle a b (n+1) k)*
        sineProduct (step a b (n+1)/2) (2*gamma a) k*
          sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/
            sineProduct (step a b (n+1)/2) (2*gamma b) n := by
  rw [weightFactor,weightProduct_sineProducts ha hb hk]
  ring

end
end jacobi.Support
