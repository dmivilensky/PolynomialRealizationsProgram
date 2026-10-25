import chebyshev2.Residual.CubicConjugate

/-!
Article: chebyshev2, Lemma 16.
The two exact cancellation identities of Lemma 17.
Use: `chebyshev2.DualCertificate.determinant_denominator` feeds
`chebyshev2.DualCertificate.determinant_cancellation` (determinant cancellation).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_stable` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set

/--
The stated quantitative bound `2 ≤ 2+q*α*U+(2-q)*R`.

Use: `chebyshev2.DualCertificate.determinant_cancellation` uses this bound to establish the
precise assertion is `(1+U*R)/(2+q*α*U+(2-q)*R)=
1/2+(U*(R-α)+(2-q)*(α*U-R)/2)/(2+q*α*U+(2-q)*R)`.

Article: chebyshev2, Theorem E.1 via `chebyshev2.DualCertificate.Data.admissible_stable`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem determinant_denominator {q U α R : ℝ}
    (hq : q ∈ Icc (0:ℝ) 2) (hU : U ∈ Icc (0:ℝ) 1)
    (hα : 0 < α) (hR : 0 ≤ R) :
    2 ≤ 2+q*α*U+(2-q)*R := by
  have h₁ : 0 ≤ q*α*U := mul_nonneg (mul_nonneg hq.1 hα.le) hU.1
  have h₂ : 0 ≤ (2-q)*R := mul_nonneg (sub_nonneg.mpr hq.2) hR
  linarith

/--
The precise assertion is `(1+U*R)/(2+q*α*U+(2-q)*R)=
1/2+(U*(R-α)+(2-q)*(α*U-R)/2)/(2+q*α*U+(2-q)*R)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates `chebyshev2.DualCertificate.determinant_denominator`
with the arguments shown in the proof.
-/
theorem determinant_cancellation {q U α R : ℝ}
    (hq : q ∈ Icc (0:ℝ) 2) (hU : U ∈ Icc (0:ℝ) 1)
    (hα : 0 < α) (hR : 0 ≤ R) :
    (1+U*R)/(2+q*α*U+(2-q)*R)=
      1/2+(U*(R-α)+(2-q)*(α*U-R)/2)/(2+q*α*U+(2-q)*R) := by
  -- Use the identities/estimates `chebyshev2.DualCertificate.determinant_denominator` with
  -- the arguments shown in the proof.
  have hd : 2+q*α*U+(2-q)*R ≠ 0 := ne_of_gt (lt_of_lt_of_le
    (by norm_num : (0:ℝ)<2) (determinant_denominator hq hU hα hR))
  apply (div_eq_iff hd).2
  rw [add_mul,div_mul_cancel₀ _ hd]
  ring

/--
Exact identity `2*V*R-q*V-(2-q)*R=2*V*(R-1)+(2-q)*(V-R)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem trace_cancellation (q V R : ℝ) :
    2*V*R-q*V-(2-q)*R=2*V*(R-1)+(2-q)*(V-R) := by ring

end
end chebyshev2.DualCertificate
