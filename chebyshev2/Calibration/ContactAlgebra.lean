import chebyshev2.Calibration.Definition
import chebyshev2.Calibration.ChainRule

/-!
Article: chebyshev2, Proposition 5.
The algebraic part of Appendix D's contact-minimum argument.
Use: `chebyshev2.Calibration.Data.F_tail_value` feeds
`chebyshev2.Calibration.ReferenceData.calibration_tail_strict` (calibration tail strict).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_Gamma` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false

/--
Defines `contactXi` of type `ℝ` by `(2-ξ)*f+ξ*r+σ*f*r-Q ξ`.

Use: `chebyshev2.Calibration.contactXi_gap` uses this definition to establish the stated
quantitative bound `(1+σ)*f*(r-f) < 2*contactXi σ ξ f r`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactXi (σ ξ f r : ℝ) : ℝ := (2-ξ)*f+ξ*r+σ*f*r-Q ξ

/--
Positivity of Xi from the two strict contact-slope inequalities.

The stated quantitative bound `0 < contactXi σ ξ f r`.

Use: `chebyshev2.Calibration.contactXi_positive_of_slopes` uses this bound to establish the
stated quantitative bound `0 < contactXi σ ξ f r`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contactXi_positive {σ ξ f r ε : ℝ} (hσ : 0 < σ) (hξ : ξ ∈ Ioo (0:ℝ) 2)
    (hε : 0 ≤ ε) (hroot : 2*ε+σ*ε^2=Q ξ) (hf : ε < f) (hr : ε < r) :
    0 < contactXi σ ξ f r := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have ha : 0 < (2-ξ)*(f-ε) := mul_pos (by linarith [hξ.2]) (sub_pos.mpr hf)
  have hb : 0 ≤ ξ*(r-ε) := mul_nonneg hξ.1.le (sub_pos.mpr hr).le
  have hc : 0 ≤ σ*ε*((f-ε)+(r-ε)) := by positivity
  have hd : 0 ≤ σ*(f-ε)*(r-ε) := by positivity
  unfold contactXi
  nlinarith

/--
The positive quadratic threshold used to compare both filters.

Constructs witnesses with the exact properties `∃ ε : ℝ, 0 < ε ∧ 2*ε+σ*ε^2=Q ξ ∧ ∀ f, 0 ≤ f → Q
ξ < 2*f+σ*f^2 → ε < f`.

Use: `chebyshev2.Calibration.contactXi_positive_of_slopes` uses this identity to establish
the stated quantitative bound `0 < contactXi σ ξ f r`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. Clear the denominators using the available nonzero hypotheses,
then verify the remaining algebraic identity.
-/
theorem quadratic_threshold {σ ξ : ℝ} (hσ : 0 < σ) (hξ : ξ ∈ Ioo (0:ℝ) 2) :
    ∃ ε : ℝ, 0 < ε ∧ 2*ε+σ*ε^2=Q ξ ∧
      ∀ f, 0 ≤ f → Q ξ < 2*f+σ*f^2 → ε < f := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let ε := (sqrt (1+σ*Q ξ)-1)/σ
  have hQ := Q_positive hξ
  have hs : 1 < sqrt (1+σ*Q ξ) := by
    rw [lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  have hsq : (sqrt (1+σ*Q ξ))^2=1+σ*Q ξ := sq_sqrt (by positivity)
  have he : 2*ε+σ*ε^2=Q ξ := by
    dsimp [ε]
    field_simp
    nlinarith
  have hp : 0 < ε := div_pos (by linarith) hσ
  refine ⟨ε,hp,he,?_⟩
  intro f hf hg
  by_contra h
  have hl : f ≤ ε := not_lt.mp h
  have hpow := pow_le_pow_left₀ hf hl 2
  have hm := mul_le_mul_of_nonneg_left hpow hσ.le
  linarith

/--
The stated quantitative bound `0 < contactXi σ ξ f r`.

Use: `chebyshev2.Calibration.contact_bracket_negative` uses this bound to establish the
stated quantitative bound `(1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r < 0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.quadratic_threshold`,
`chebyshev2.Calibration.contactXi_positive` with the arguments shown in the proof.
-/
theorem contactXi_positive_of_slopes {σ ξ f r : ℝ} (hσ : 0 < σ)
    (hξ : ξ ∈ Ioo (0:ℝ) 2) (hf : 0 ≤ f) (hr : 0 ≤ r)
    (hLf : Q ξ < 2*f+σ*f^2) (hRr : Q ξ < 2*r+σ*r^2) :
    0 < contactXi σ ξ f r := by
  obtain ⟨ε,hε,he,hb⟩ := quadratic_threshold hσ hξ
  exact contactXi_positive hσ hξ hε.le he (hb f hf hLf) (hb r hr hRr)

/--
Equation (47), after substituting the contact derivative of g.

The precise assertion is `(2*((f+r)-2*(q-(ξ-f)))*(2+σ*(f+r))- 2*((r-f)*(2+σ*(f+r))/(2*f+σ*f^2-Q
ξ))* ((q^2-2*(ξ-f))+σ*(q-(ξ-f))^2))/(2+σ*(f+r))^2= 2*(q-ξ)/((2+σ*(f+r))*(2*f+σ*f^2-Q ξ))*
((1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 5.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem contact_derivative_factorization {σ q ξ f r : ℝ}
    (hΔ : 2+σ*(f+r) ≠ 0) (hD : 2*f+σ*f^2-Q ξ ≠ 0) :
    (2*((f+r)-2*(q-(ξ-f)))*(2+σ*(f+r))-
      2*((r-f)*(2+σ*(f+r))/(2*f+σ*f^2-Q ξ))*
        ((q^2-2*(ξ-f))+σ*(q-(ξ-f))^2))/(2+σ*(f+r))^2=
    2*(q-ξ)/((2+σ*(f+r))*(2*f+σ*f^2-Q ξ))*
      ((1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold contactXi Q at *
  field_simp (disch := solve | norm_num | assumption | (convert hΔ using 1; ring) |
    (convert hD using 1; ring))
  ring

/--
The strictly positive gap in the difficult q < xi < 1 case.

The stated quantitative bound `(1+σ)*f*(r-f) < 2*contactXi σ ξ f r`.

Use: `chebyshev2.Calibration.contact_bracket_negative` uses this bound to establish the
stated quantitative bound `(1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r < 0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contactXi_gap {σ ξ f r ε : ℝ} (hσ : 0 < σ) (hξ : ξ ∈ Ioo (0:ℝ) 1)
    (hε : 0 ≤ ε) (hroot : 2*ε+σ*ε^2=Q ξ) (hf : ε < f) (hr : ε < r)
    (hfξ : f ≤ ξ) : (1+σ)*f*(r-f) < 2*contactXi σ ξ f r := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hA : 0 < (f-ε)*(4-2*ξ+(3*σ+1)*ε) := by
    apply mul_pos (sub_pos.mpr hf)
    have hm : 0 ≤ (3*σ+1)*ε := mul_nonneg (by linarith) hε
    linarith [hξ.2]
  have hB : 0 ≤ (r-ε)*(2*ξ+(σ-1)*f) := by
    apply mul_nonneg (sub_pos.mpr hr).le
    have hp : 0 ≤ σ*f := mul_nonneg hσ.le (hε.trans hf.le)
    nlinarith [hξ.1]
  have hC : 0 ≤ (σ+1)*(f-ε)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hid : 2*contactXi σ ξ f r-(1+σ)*f*(r-f)=
      (f-ε)*(4-2*ξ+(3*σ+1)*ε)+(r-ε)*(2*ξ+(σ-1)*f)+(σ+1)*(f-ε)^2 := by
    unfold contactXi
    linear_combination 2*hroot
  linarith

/--
Sign of the bracket in (47) on the lower half of the q interval.

The stated quantitative bound `(1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r < 0`.

Use: `chebyshev2.Calibration.ReferenceData.contact_bracket_negative_interior` uses this
bound to prove the bound `(1+σ)*(R.filter hσ x-R.filter hσ
(-x))*(q-R.referenceSpeed.q x)- 2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter
hσ (-x)) < 0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `ξ < 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem contact_bracket_negative {σ q ξ f r : ℝ} (hσ : 0 < σ)
    (hq : q ∈ Ioc (0:ℝ) 1) (hξ : ξ ∈ Ioo (0:ℝ) 2)
    (hf : 0 ≤ f) (hr : 0 ≤ r) (hfξ : f ≤ ξ) (hh : ξ-f ≤ q)
    (hLf : Q ξ < 2*f+σ*f^2) (hRr : Q ξ < 2*r+σ*r^2)
    (hleft : ξ < 1 → f < r) (hright : 1 ≤ ξ → r ≤ f) :
    (1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r < 0 := by
  -- Separate `ξ < 1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hXi := contactXi_positive_of_slopes hσ hξ hf hr hLf hRr
  by_cases hl : ξ < 1
  · have hfr := hleft hl
    by_cases hqξ : ξ ≤ q
    · have hm : (1+σ)*(f-r)*(q-ξ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hfr.le))
          (sub_nonneg.mpr hqξ)
      linarith
    · obtain ⟨ε,hε,he,hb⟩ := quadratic_threshold hσ hξ
      have hgap := contactXi_gap hσ ⟨hξ.1,hl⟩ hε.le he (hb f hf hLf) (hb r hr hRr) hfξ
      have hm : (1+σ)*(r-f)*(ξ-q) ≤ (1+σ)*(r-f)*f :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) (sub_nonneg.mpr hfr.le))
      nlinarith
  · have hfr := hright (not_lt.mp hl)
    have hqξ : q ≤ ξ := hq.2.trans (not_lt.mp hl)
    have hm : (1+σ)*(f-r)*(q-ξ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by linarith) (sub_nonneg.mpr hfr)) (sub_nonpos.mpr hqξ)
    linarith

/--
Contact parametrization removes the inverse derivative from (47).

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt
(R.contactFunctional hσ q) (R.contactDerivative hσ q x) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem contact_flow_factorization {σ q ξ f r M : ℝ} (hΔ : 2+σ*(f+r) ≠ 0) :
    ((4*(q-(ξ-f))*(-((M-Q ξ)-(M-2*f-σ*f^2)))-
      (-2*((M-Q ξ)-(M-2*f-σ*f^2)))*(f+r)-
      (q^2-2*(ξ-f))*((M-2*f-σ*f^2)-(M-2*r-σ*r^2)))*(2+σ*(f+r))-
      (2*(q-(ξ-f))^2-(q^2-2*(ξ-f))*(f+r))*
        (σ*((M-2*f-σ*f^2)-(M-2*r-σ*r^2))))/(2+σ*(f+r))^2=
    2*(q-ξ)/(2+σ*(f+r))*((1+σ)*(f-r)*(q-ξ)-2*contactXi σ ξ f r) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold contactXi Q
  field_simp (disch := solve | assumption | (convert hΔ using 1; ring))
  ring

/--
The h > q comparison needs only the monotonicity of h+g(h). Clearing both positive denominators
gives a sum of two nonnegative terms.

The stated quantitative bound `Q q*G/(2+σ*G) ≤ (2*a^2+(Q q+2*a)*g)/(2+σ*g)`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_beyond_diagonal` uses this bound to
establish the stated quantitative bound `(R.calibration hσ hb hω).F q q ≤ (R.calibration hσ hb
hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Q_nonneg` with the arguments
shown in the proof.
-/
theorem beyond_diagonal {σ q G g a : ℝ} (hσ : 0 < σ)
    (hq : q ∈ Icc (0:ℝ) 2) (hG : 0 ≤ G) (hg : 0 ≤ g) (ha : 0 ≤ a)
    (hmon : G-a ≤ g) (hthreshold : Q q ≤ 2*G+σ*G^2) :
    Q q*G/(2+σ*G) ≤ (2*a^2+(Q q+2*a)*g)/(2+σ*g) := by
  -- Use the identities/estimates `chebyshev2.Calibration.Q_nonneg` with the arguments
  -- shown in the proof.
  apply (div_le_div_iff₀ (by positivity : 0<2+σ*G) (by positivity : 0<2+σ*g)).2
  have h1 : 0 ≤ 2*a*(2*G+σ*G^2-Q q) := by positivity
  have h2 : 0 ≤ 2*(a*(2+σ*G)+Q q)*(g-G+a) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg ha (by positivity)) (Q_nonneg hq))
    · linarith
  nlinarith

namespace Data
variable (C : Data)

/--
The derivative in h before the contact substitution.

The actual derivative at the stated point: `HasDerivAt (C.F q) ((2*(C.potential
h-2*(q-h))*(2+C.sigma*C.potential h)- 2*g'*((q^2-2*h)+C.sigma*(q-h)^2))/(2+C.sigma*C.potential
h)^2) h`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 5.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.denominator_positive` with
the arguments shown in the proof.
-/
theorem F_hasDerivAt {q h g' : ℝ} (hg : HasDerivAt C.potential g' h) :
    HasDerivAt (C.F q)
      ((2*(C.potential h-2*(q-h))*(2+C.sigma*C.potential h)-
        2*g'*((q^2-2*h)+C.sigma*(q-h)^2))/(2+C.sigma*C.potential h)^2) h := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.denominator_positive` with
  -- the arguments shown in the proof.
  have hA : HasDerivAt (fun t => q-t) (-1) h :=
    by convert! (hasDerivAt_const h q).sub (hasDerivAt_id h) using 1; norm_num
  have hB : HasDerivAt (fun t => q^2-2*t) (-2) h :=
    by convert! (hasDerivAt_const h (q^2)).sub ((hasDerivAt_id h).const_mul 2) using 1; norm_num
  have hp := (((hA.pow 2).const_mul 2).sub (hB.mul hg)).div
    ((hasDerivAt_const h 2).add (hg.const_mul C.sigma)) (C.denominator_positive h).ne'
  convert hp using 1
  · rfl
  · simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
    ring

/--
The value at contact, used in the exactness and symmetry arguments.

Exact identity `C.F q (q-f)=(Q q*(f+r)-2*f*r)/(2+C.sigma*(f+r))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 5.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem F_contact_value {q f r : ℝ} (hg : C.potential (q-f)=f+r) :
    C.F q (q-f)=(Q q*(f+r)-2*f*r)/(2+C.sigma*(f+r)) := by
  unfold F
  rw [hg]
  unfold Q
  congr 1
  ring

/--
On the linear tail g(h)=2-h, F has the printed positive derivative.

Exact identity `C.F q h=h*(2-q)^2/(2+C.sigma*(2-h))`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_Gamma_at_X` rewrites with this
identity to establish `(R.calibration hσ hb hω).Gamma q=
(R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem F_tail_value {q h : ℝ} (hg : C.potential h=2-h) :
    C.F q h=h*(2-q)^2/(2+C.sigma*(2-h)) := by
  unfold F
  rw [hg]
  congr 1
  ring

end Data
end
end chebyshev2.Calibration
