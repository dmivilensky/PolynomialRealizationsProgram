import «2606.16671v2».Chebyshev.RationalEvaluation
import «2606.16671v2».Chebyshev.Amplification

/-!
Article: 2606.16671v2, Remark 5.5.
Exact rational certificates for the three static-shift amplification factors in 5.5.
Result: `«2606.16671v2».amplification_certificate_quarter` supplies the stated article conclusion.
-/
namespace «2606.16671v2»
open Polynomial Polynomial.Chebyshev

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/--
The common Chebyshev terminal factor in the κ=10000, N=725 example.

The stated quantitative bound `(1008/10^9:ℝ) < 1/(T ℝ (725:ℕ)).eval (10001/9999) ∧ 1/(T ℝ
(725:ℕ)).eval (10001/9999) < (1009/10^9:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments
shown in the proof.
-/
theorem terminal_certificate :
    (1008/10^9:ℝ) < 1/(T ℝ (725:ℕ)).eval (10001/9999) ∧
      1/(T ℝ (725:ℕ)).eval (10001/9999) < (1009/10^9:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments shown
  -- in the proof.
  have hx : ((10001/9999:ℚ):ℝ) = (10001/9999:ℝ) := by norm_num
  rw [← hx, ← chebyshevPair_real]
  have hq : (1008/10^9:ℚ) < 1/(chebyshevPair (10001/9999) 725).1 ∧
      1/(chebyshevPair (10001/9999) 725).1 < (1009/10^9:ℚ) := by
    norm_num [chebyshevPair]
  have hc := And.intro ((Rat.cast_lt (K := ℝ)).mpr hq.1)
    ((Rat.cast_lt (K := ℝ)).mpr hq.2)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] at hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow]
  exact hc

/--
Exact rational certificates for the three static-shift amplification factors in 5.5.

The stated quantitative bound `(224/100:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/100)/9999) ∧ (T ℝ
(725:ℕ)).eval (1+2*(1/100)/9999) < (225/100:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments
shown in the proof.
-/
theorem amplification_certificate_one_percent :
    (224/100:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/100)/9999) ∧
      (T ℝ (725:ℕ)).eval (1+2*(1/100)/9999) < (225/100:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments shown
  -- in the proof.
  have hx : ((1+2*(1/100)/9999:ℚ):ℝ) = (1+2*(1/100)/9999:ℝ) := by norm_num
  rw [← hx, ← chebyshevPair_real]
  have hq : (224/100:ℚ) < (chebyshevPair (1+2*(1/100)/9999) 725).1 ∧
      (chebyshevPair (1+2*(1/100)/9999) 725).1 < (225/100:ℚ) := by
    norm_num [chebyshevPair]
  have hc := And.intro ((Rat.cast_lt (K := ℝ)).mpr hq.1)
    ((Rat.cast_lt (K := ℝ)).mpr hq.2)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] at hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow]
  exact hc

/--
The stated quantitative bound `(128/10:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/20)/9999) ∧ (T ℝ
(725:ℕ)).eval (1+2*(1/20)/9999) < (129/10:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments
shown in the proof.
-/
theorem amplification_certificate_five_percent :
    (128/10:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/20)/9999) ∧
      (T ℝ (725:ℕ)).eval (1+2*(1/20)/9999) < (129/10:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments shown
  -- in the proof.
  have hx : ((1+2*(1/20)/9999:ℚ):ℝ) = (1+2*(1/20)/9999:ℝ) := by norm_num
  rw [← hx, ← chebyshevPair_real]
  have hq : (128/10:ℚ) < (chebyshevPair (1+2*(1/20)/9999) 725).1 ∧
      (chebyshevPair (1+2*(1/20)/9999) 725).1 < (129/10:ℚ) := by
    norm_num [chebyshevPair]
  have hc := And.intro ((Rat.cast_lt (K := ℝ)).mpr hq.1)
    ((Rat.cast_lt (K := ℝ)).mpr hq.2)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] at hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow]
  exact hc

/--
The stated quantitative bound `(704:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/4)/9999) ∧ (T ℝ
(725:ℕ)).eval (1+2*(1/4)/9999) < (705:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Remark 5.5.

Proof: Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments
shown in the proof.
-/
theorem amplification_certificate_quarter :
    (704:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/4)/9999) ∧
      (T ℝ (725:ℕ)).eval (1+2*(1/4)/9999) < (705:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».chebyshevPair_real` with the arguments shown
  -- in the proof.
  have hx : ((1+2*(1/4)/9999:ℚ):ℝ) = (1+2*(1/4)/9999:ℝ) := by norm_num
  rw [← hx, ← chebyshevPair_real]
  have hq : (704:ℚ) < (chebyshevPair (1+2*(1/4)/9999) 725).1 ∧
      (chebyshevPair (1+2*(1/4)/9999) 725).1 < (705:ℚ) := by
    norm_num [chebyshevPair]
  have hc := And.intro ((Rat.cast_lt (K := ℝ)).mpr hq.1)
    ((Rat.cast_lt (K := ℝ)).mpr hq.2)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] at hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow]
  exact hc

end «2606.16671v2»
