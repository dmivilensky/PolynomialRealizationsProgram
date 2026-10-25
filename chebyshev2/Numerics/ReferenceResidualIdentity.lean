import chebyshev2.Numerics.ReferenceJetSource
import chebyshev2.Numerics.ResidualFlow

/-!
Article: chebyshev2, Section 4.1.
Cancellation-preserving reference residuals.
Use: `chebyshev2.Numerics.ReferenceResidual.polynomial_residual_bound` feeds
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.Summary.sound` (sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open Set Real chebyshev2.Calibration
set_option autoImplicit false

/--
An approximate cubic root is validated by its residual and a lower bound for the secant slope
on a common interval containing both roots.

The stated quantitative bound `|r-z| ≤ η/m`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cubic_residual_error {a b r z l m η : ℝ}
    (hr : r^3-a*r-b = 0) (hl : 0 ≤ l) (hlr : l ≤ r) (hlz : l ≤ z)
    (hm : 0 < m) (hs : m ≤ 3*l^2-a) (he : |z^3-a*z-b| ≤ η) :
    |r-z| ≤ η/m := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hrr : l^2 ≤ r^2 := by nlinarith
  have hzz : l^2 ≤ z^2 := by nlinarith
  have hrz : l^2 ≤ r*z := by nlinarith [mul_nonneg (sub_nonneg.mpr hlr) (sub_nonneg.mpr hlz)]
  have hd : m ≤ z^2+z*r+r^2-a := by nlinarith
  have heq : z^3-a*z-b = (z-r)*(z^2+z*r+r^2-a) := by nlinarith [hr]
  rw [heq, abs_mul, abs_of_pos (hm.trans_le hd)] at he
  rw [le_div_iff₀ hm, abs_sub_comm]
  exact (mul_le_mul_of_nonneg_left hd (abs_nonneg _)).trans he

/--
For the positive root, its defining equation supplies the missing lower bound on the secant
slope. No enclosure of the true root is a premise.

The stated quantitative bound `|r-z|≤η/(k*l^2)`.

Use: `chebyshev2.Numerics.ReferenceResidual.polynomial_residual_bound` uses this bound to
establish the stated quantitative bound `|R.normalizedVelocity t*(R.k*(t*R.normalizedRoot
t)^2-2*p-σ*p^2)-pd|≤η`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem positive_cubic_residual_error {k a b r z l η : ℝ}
    (hk : 0<k) (hb : 0<b) (hr : 0<r) (heq : k*r^3-a*r-b=0)
    (hl : 0<l) (hz : l≤z) (he : |k*z^3-a*z-b|≤η) :
    |r-z|≤η/(k*l^2) := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hbase : 0≤k*r^2-a := by
    by_contra! hn
    have hh := mul_neg_of_neg_of_pos hn hr
    nlinarith [hh]
  have hzz : l^2≤z^2 := by nlinarith
  have hzr : 0≤z*r := mul_nonneg (hl.le.trans hz) hr.le
  have hs : k*l^2≤k*(z^2+z*r+r^2)-a := by nlinarith
  have hm : 0<k*l^2 := mul_pos hk (sq_pos_of_pos hl)
  have hid : k*z^3-a*z-b=(z-r)*(k*(z^2+z*r+r^2)-a) := by nlinarith [heq]
  rw [hid, abs_mul, abs_of_pos (hm.trans_le hs)] at he
  rw [le_div_iff₀ hm, abs_sub_comm]
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans he

namespace ReferenceResidual
variable (R : ReferenceData)

/--
Defines `denominator` of type `ℝ` by `R.k * (R.normalizedRoot t)^2 - t*(2-t^3)`.

Use: `chebyshev2.Numerics.ReferenceResidual.denominator_eq_speed` uses this definition to
establish exact identity `denominator R t = R.normalizedSpeed t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def denominator (t : ℝ) : ℝ :=
  R.k * (R.normalizedRoot t)^2 - t*(2-t^3)

/--
Exact identity `denominator R t = R.normalizedSpeed t`.

Use: `chebyshev2.Numerics.ReferenceResidual.denominator_positive` rewrites with this
identity to prove the bound `0 < denominator R t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem denominator_eq_speed {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    denominator R t = R.normalizedSpeed t := by
  have hr := R.normalizedRoot_spec ht
  have he := hr.2
  unfold cubic at he
  unfold denominator ReferenceData.normalizedSpeed
  field_simp [hr.1.ne']
  nlinarith [he]

/--
The stated quantitative bound `0 < denominator R t`.

Use: `chebyshev2.Numerics.ReferenceResidual.origin_residual` uses this bound to establish
exact identity `R.normalizedVelocity t * (R.k*(t*R.normalizedRoot t)^2-2*t^3-σ*(t^3)^2)-3*t^2 =
-(σ+1)*R.normalizedVelocity t*t^6`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.ReferenceResidual.denominator_eq_speed`,
`chebyshev2.Calibration.ReferenceData.normalizedSpeed_positive` with the arguments shown in
the proof.
-/
theorem denominator_positive {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < denominator R t := by
  rw [denominator_eq_speed R ht]
  exact R.normalizedSpeed_positive ht

/--
Defines `numerator` of type `ℝ` by `R.k*(3*t^2-p' t)*(R.normalizedRoot t)^2 + p'
t*(t*(2-t^3))-6*p t-3*σ*(p t)^2`.

Use: `chebyshev2.Numerics.ReferenceResidual.numerator_approximation` uses this definition
to establish the identity `numerator R σ p p' t = (R.k*(3*t^2-p' t)*(z t)^2+p'
t*(t*(2-t^3))-6*p t-3*σ*(p t)^2) + R.k*(3*t^2-p' t)*((R.normalizedRoot t)^2-(z t)^2)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def numerator (σ : ℝ) (p p' : ℝ → ℝ) (t : ℝ) : ℝ :=
  R.k*(3*t^2-p' t)*(R.normalizedRoot t)^2 +
    p' t*(t*(2-t^3))-6*p t-3*σ*(p t)^2

/--
Exact identity `R.normalizedVelocity t * (R.k*(t*R.normalizedRoot t)^2-2*p t-σ*(p t)^2)-p' t =
numerator R σ p p' t / denominator R t`.

Use: `chebyshev2.Numerics.ReferenceResidual.origin_residual` rewrites with this identity to
establish exact identity `R.normalizedVelocity t * (R.k*(t*R.normalizedRoot
t)^2-2*t^3-σ*(t^3)^2)-3*t^2 = -(σ+1)*R.normalizedVelocity t*t^6`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem residual_identity {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (σ : ℝ) (p p' : ℝ → ℝ) :
    R.normalizedVelocity t * (R.k*(t*R.normalizedRoot t)^2-2*p t-σ*(p t)^2)-p' t =
      numerator R σ p p' t / denominator R t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [ReferenceData.normalizedVelocity, ← denominator_eq_speed R ht]
  unfold numerator
  field_simp [(denominator_positive R ht).ne']
  unfold denominator
  ring

/--
The nonlinear dependence on the true root is confined to its square. All other terms can be
checked as a single polynomial, retaining cancellation.

Exact identity `numerator R σ p p' t = (R.k*(3*t^2-p' t)*(z t)^2+p' t*(t*(2-t^3))-6*p t-3*σ*(p
t)^2) + R.k*(3*t^2-p' t)*((R.normalizedRoot t)^2-(z t)^2)`.

Use: `chebyshev2.Numerics.ReferenceResidual.polynomial_residual_bound` rewrites with this
identity to prove the bound `|R.normalizedVelocity
t*(R.k*(t*R.normalizedRoot t)^2-2*p-σ*p^2)-pd|≤η`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem numerator_approximation (σ : ℝ) (p p' z : ℝ → ℝ) (t : ℝ) :
    numerator R σ p p' t =
      (R.k*(3*t^2-p' t)*(z t)^2+p' t*(t*(2-t^3))-6*p t-3*σ*(p t)^2) +
      R.k*(3*t^2-p' t)*((R.normalizedRoot t)^2-(z t)^2) := by
  unfold numerator
  ring

/--
Exact identity `R.normalizedVelocity t * (R.k*(t*R.normalizedRoot t)^2-2*t^3-σ*(t^3)^2)-3*t^2 =
-(σ+1)*R.normalizedVelocity t*t^6`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem origin_residual {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (σ : ℝ) :
    R.normalizedVelocity t * (R.k*(t*R.normalizedRoot t)^2-2*t^3-σ*(t^3)^2)-3*t^2 =
      -(σ+1)*R.normalizedVelocity t*t^6 := by
  rw [residual_identity R ht σ (fun x => x^3) (fun x => 3*x^2)]
  rw [ReferenceData.normalizedVelocity, ← denominator_eq_speed R ht]
  unfold numerator
  field_simp [(denominator_positive R ht).ne']
  ring

/--
A root residual and an ODE residual polynomial suffice for a true RHS bound. The true root and
the true filter never occur in the numerical input.

The stated quantitative bound `|R.normalizedVelocity t*(R.k*(t*R.normalizedRoot
t)^2-2*p-σ*p^2)-pd|≤η`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Summary.sound` uses this bound to
establish the stated quantitative bound `0≤p ∧ |R.normalizedVelocity t*(R.k*(t*R.normalizedRoot
t)^2-2*p-σ*p^2)-pd|≤(η:ℝ)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem polynomial_residual_bound {t z p pd d kl l u δ er eo ef η σ : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hd : 0<d) (_hkl : 0<kl) (hk : kl≤R.k)
    (hl : 0<l) (hz : z∈Icc l u) (hδ : 0≤δ) (hδl : δ≤l/2)
    (hr : |d*(R.k*z^3-3*t*(2-t^3)*z-2*R.b (t^3*(2-t^3))*(2-t^3))|≤er)
    (hroot : er≤δ*(d*kl*l^2))
    (ho : |R.k*(3*t^2-pd)*z^2+pd*t*(2-t^3)-6*p-3*σ*p^2|≤eo)
    (hf : |R.k*(3*t^2-pd)|≤ef) (hef : 0≤ef) (hη : 0≤η)
    (hbudget : eo+ef*δ*(2*u+δ)≤η*(kl*l^2/6)) :
    |R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-2*p-σ*p^2)-pd|≤η := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let r := R.normalizedRoot t
  have hrpos : 0<r := (R.normalizedRoot_spec ht).1
  have heq := (R.normalizedRoot_spec ht).2
  change R.k*r^3-3*(t*(2-t^3))*r-2*R.b (t^3*(2-t^3))*(2-t^3)=0 at heq
  have hh : 0<2-t^3 := by have hc := chebyshev2.DualCertificate.cube_mem ht; linarith [hc.2]
  have hb : 0<2*R.b (t^3*(2-t^3))*(2-t^3) :=
    mul_pos (mul_pos (by norm_num) (R.positive _ (ReferenceData.normalized_coefficient_mem ht))) hh
  have hres : |R.k*z^3-3*(t*(2-t^3))*z-2*R.b (t^3*(2-t^3))*(2-t^3)|≤er/d := by
    rw [le_div_iff₀ hd]
    simpa [abs_mul, abs_of_pos hd, mul_comm, mul_left_comm, mul_assoc] using hr
  have herror := positive_cubic_residual_error R.k_positive hb hrpos heq hl hz.1 hres
  have herror' : |r-z|≤δ := herror.trans (by
    rw [div_le_iff₀ (mul_pos R.k_positive (sq_pos_of_pos hl)), div_le_iff₀ hd]
    calc
      er ≤ δ*(d*kl*l^2) := hroot
      _ ≤ δ*(d*R.k*l^2) := by gcongr
      _ = δ*(R.k*l^2)*d := by ring)
  have herr := abs_le.mp herror'
  have hrlo : l/2≤r := by linarith [hz.1]
  have hru : r≤u+δ := by linarith [hz.2]
  have hbase : 0≤R.k*r^2-3*(t*(2-t^3)) := by
    by_contra! hn
    have hh' := mul_neg_of_neg_of_pos hn hrpos
    nlinarith [hh']
  have hr2 : l^2/4≤r^2 := by nlinarith
  have hprod : kl*(l^2/4)≤R.k*r^2 :=
    mul_le_mul hk hr2 (by positivity) R.k_positive.le
  have hden : kl*l^2/6≤denominator R t := by
    unfold denominator
    change kl*l^2/6≤R.k*r^2-t*(2-t^3)
    nlinarith
  have hsum : |r+z|≤2*u+δ := by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2]
  have hsq : |r^2-z^2|≤δ*(2*u+δ) := by
    have hid : r^2-z^2=(r-z)*(r+z) := by ring
    rw [hid, abs_mul]
    exact mul_le_mul herror' hsum (abs_nonneg _) hδ
  have hnum : |numerator R σ (fun _ => p) (fun _ => pd) t|≤η*(kl*l^2/6) := by
    rw [numerator_approximation R σ (fun _ => p) (fun _ => pd) (fun _ => z)]
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [mul_assoc] using ho) ?_).trans hbudget)
    rw [abs_mul]
    simpa only [mul_assoc] using mul_le_mul hf hsq (abs_nonneg _) hef
  rw [residual_identity R ht σ (fun _ => p) (fun _ => pd), abs_div,
    abs_of_pos (denominator_positive R ht), div_le_iff₀ (denominator_positive R ht)]
  exact hnum.trans (mul_le_mul_of_nonneg_left hden hη)

end ReferenceResidual
end chebyshev2.Numerics
