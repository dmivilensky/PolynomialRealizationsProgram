import chebyshev2.Numerics.IntegerResidualChain

/-!
Article: chebyshev2, Section 4.1.
The root enclosures already checked for the ODE residual are also value enclosures for quadrature.
Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.check_root_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.root_error_left` (root error left).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open Set chebyshev2.Calibration
set_option autoImplicit false

/--
The stated quantitative bound `|R.normalizedRoot t-z|≤δ`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Summary.root_error` uses this
bound to prove the bound `|R.normalizedRoot t-z|≤(δ:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedRoot_spec`,
`chebyshev2.DualCertificate.cube_mem`,
`chebyshev2.Calibration.ReferenceData.normalized_coefficient_mem` with the arguments shown
in the proof.
-/
theorem ReferenceResidual.root_error {R : ReferenceData} {t z d kl l δ er : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hd : 0<d) (hk : kl≤R.k) (hl : 0<l)
    (hz : l≤z) (hδ : 0≤δ)
    (hr : |d*(R.k*z^3-3*t*(2-t^3)*z-2*R.b (t^3*(2-t^3))*(2-t^3))|≤er)
    (hbudget : er≤δ*(d*kl*l^2)) : |R.normalizedRoot t-z|≤δ := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.normalizedRoot_spec`,
  -- `chebyshev2.DualCertificate.cube_mem`,
  -- `chebyshev2.Calibration.ReferenceData.normalized_coefficient_mem` with the arguments
  -- shown in the proof.
  have heq := (R.normalizedRoot_spec ht).2
  change R.k*(R.normalizedRoot t)^3-3*(t*(2-t^3))*R.normalizedRoot t-
    2*R.b (t^3*(2-t^3))*(2-t^3)=0 at heq
  have hh : 0<2-t^3 := by
    have hc := chebyshev2.DualCertificate.cube_mem ht
    linarith [hc.2]
  have hb : 0<2*R.b (t^3*(2-t^3))*(2-t^3) :=
    mul_pos (mul_pos (by norm_num)
      (R.positive _ (ReferenceData.normalized_coefficient_mem ht))) hh
  have hres : |R.k*z^3-3*(t*(2-t^3))*z-2*R.b (t^3*(2-t^3))*(2-t^3)|≤er/d := by
    rw [le_div_iff₀ hd]
    simpa [abs_mul,abs_of_pos hd,mul_comm,mul_left_comm,mul_assoc] using hr
  refine (positive_cubic_residual_error R.k_positive hb
    (R.normalizedRoot_spec ht).1 heq hl hz hres).trans ?_
  rw [div_le_iff₀ (mul_pos R.k_positive (sq_pos_of_pos hl)),div_le_iff₀ hd]
  calc
    er≤δ*(d*kl*l^2) := hbudget
    _≤δ*(d*R.k*l^2) := by gcongr
    _=δ*(R.k*l^2)*d := by ring

namespace IntegerCertificate.ResidualCell
open Polynomial chebyshev2.DualCertificate
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `|R.normalizedRoot t-z|≤(δ:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.check_root_sound` uses this bound
to prove the bound `|(ReferenceJetSource.referenceData
R).normalizedRoot ((values s r 0).eval x)- (values s r 2).eval x|≤(r.delta:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.Bounds.real_mem`,
`chebyshev2.Numerics.ReferenceResidual.root_error`,
`chebyshev2.Numerics.IntegerCertificate.Bounds.real_abs` with the arguments shown in the
proof.
-/
theorem Summary.root_error {s : Nat} {b : Summary} {δ η : ℚ}
    (hc : b.check s δ η=true) (R : ReferenceData) {t z d : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hk : b.k.Mem s R.k) (hd : b.den.Mem s d)
    (hz : b.z.Mem s z)
    (hr : b.root.Mem s (d*(R.k*z^3-3*t*(2-t^3)*z-
      2*R.b (t^3*(2-t^3))*(2-t^3)))) : |R.normalizedRoot t-z|≤(δ:ℝ) := by
  -- Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.Bounds.real_mem`,
  -- `chebyshev2.Numerics.ReferenceResidual.root_error`,
  -- `chebyshev2.Numerics.IntegerCertificate.Bounds.real_abs` with the arguments shown in
  -- the proof.
  obtain ⟨hs,hD,_,hL,hδ,_,_,_,_,hroot,_⟩ := of_decide_eq_true hc
  have hDr : (0:ℝ)<(b.den.lower s:ℝ) := by exact_mod_cast hD
  have hLr : (0:ℝ)<(b.z.lower s:ℝ) := by exact_mod_cast hL
  have hδr : (0:ℝ)≤(δ:ℝ) := by exact_mod_cast hδ
  have hrootr : (b.root.magnitude s:ℝ)≤(δ:ℝ)*
      ((b.den.lower s:ℝ)*(b.k.lower s:ℝ)*(b.z.lower s:ℝ)^2) := by exact_mod_cast hroot
  have hd' := Bounds.real_mem hs hd
  apply ReferenceResidual.root_error ht (hDr.trans_le hd'.1)
    (Bounds.real_mem hs hk).1 hLr (Bounds.real_mem hs hz).1 hδr (Bounds.real_abs hs hr)
  exact hrootr.trans (by gcongr; exact hd'.1)

/--
The stated quantitative bound `|(ReferenceJetSource.referenceData R).normalizedRoot ((values s
r 0).eval x)- (values s r 2).eval x|≤(r.delta:ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.root_error_left` uses this
bound to prove the bound `|(ReferenceJetSource.referenceData
R).normalizedRoot t- (Poly.exactPolynomial s r.z).eval (r.localCoordinate s t)|≤(r.delta:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.sourceRange_sound`,
`chebyshev2.Numerics.IntegerCertificate.ResidualExpr.values_basic`,
`chebyshev2.Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in the
proof.
-/
theorem check_root_sound {s : Nat} (hs : 0<s) {ops : List Op} {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (R : RationalReference) (η : ℚ)
    (shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true)
    (shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts R).1=true)
    (shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual R)=true)
    {r : Row} (hc : check s ops piB η r=true) {x : ℝ} (hx : x∈Icc (0:ℝ) 1)
    (ht : (values s r 0).eval x∈Icc (0:ℝ) 1) :
    |(ReferenceJetSource.referenceData R).normalizedRoot ((values s r 0).eval x)-
      (values s r 2).eval x|≤(r.delta:ℝ) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualCell.sourceRange_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualExpr.values_basic`,
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.range_sound` with the arguments shown in
  -- the proof.
  have hboth : decide (0<r.width ∧ r.width*r.step=s)=true ∧
      (summarize s ops piB r).any (Summary.check s r.delta η)=true := by
    simpa only [check,Bool.and_eq_true] using hc
  have hcheck := hboth.2
  cases he : summarize s ops piB r with
  | none => simp [he] at hcheck
  | some b =>
    have hb : b.check s r.delta η=true := by simpa [he] using hcheck
    obtain ⟨out,hout,K,hK,D,hD,N,hN,F,hF,E,hE,Z,hZ,P,hP,heq⟩ :
        ∃ out, Poly.Taylor.evalProgram s r.degree (inputs s piB r) r.checkpoints ops=some out ∧
        ∃ K, outputRange s out 72=some K ∧
        ∃ D, outputRange s out 30=some D ∧
        ∃ N, outputRange s out 16=some N ∧
        ∃ F, outputRange s out 12=some F ∧
        ∃ E, outputRange s out 0=some E ∧
        ∃ Z, Poly.range s ⟨0,s⟩ (Poly.exactBounds r.z)=some Z ∧
        ∃ P, Poly.range s ⟨0,s⟩ (Poly.exactBounds r.p)=some P ∧
        Summary.mk K D N F E Z P=b := by
      simpa only [summarize,Option.bind_eq_bind,Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    subst b
    have hK' := sourceRange_sound hs hpi hout shapeK hK hx
    have hD' := sourceRange_sound hs hpi hout shapeD hD hx
    have hN' := sourceRange_sound hs hpi hout shapeRoot hN hx
    rw [values_eval] at hK' hD' hN'
    have hbasic := ResidualExpr.values_basic ((values s r 0).eval x)
      ((values s r 2).eval x) ((values s r 3).eval x) ((values s r 4).eval x)
    rw [hbasic.2.2.2.2.1] at hK'
    rw [ResidualExpr.rootResidual_value R ht] at hN'
    have hxi : (⟨0,s⟩:Bounds).Mem s x := by
      constructor <;> dsimp [Bounds.Mem]
      · simpa using mul_nonneg (Nat.cast_nonneg s) hx.1
      · simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)
    have hZ' := Poly.range_sound hs (Poly.exactBounds_sound hs r.z) hxi hZ
    exact Summary.root_error hb (ReferenceJetSource.referenceData R) ht hK' hD' hZ' hN'

end IntegerCertificate.ResidualCell
end chebyshev2.Numerics
