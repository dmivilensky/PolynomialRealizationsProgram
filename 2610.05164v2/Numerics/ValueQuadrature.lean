import «2610.05164v2».Numerics.PolynomialIntegral
import «2610.05164v2».Certificates.Partition

/-!
Article: 2610.05164v2, Section 4.1.
Ordered quadrature from value residuals, without higher derivative enclosures.
Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error_cover` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` (amplitude integral
error).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.Poly
noncomputable section
open Set MeasureTheory «2610.05164v2».Certificates LeanCert.Core
set_option autoImplicit false

/--
A rational integration cell, polynomial primitive and uniform derivative-residual budget. The
integral enclosure follows from endpoint differences plus the proved residual error.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.totalCenter` uses this record of data and
proof obligations in the displayed construction of `totalCenter`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure ValuePanel where
  /-- Closed rational integration cell. -/
  domain : Cell
  /-- Scaled polynomial coefficients of the proposed primitive. -/
  coefficients : List Int
  /-- Uniform derivative-residual budget converting primitive endpoint differences into an integral enclosure. -/
  error : ℚ

/--
Defines `ValuePanel.center` of type `ℚ` by `(p.domain.hi-p.domain.lo)*integralCoefficients s 0
p.coefficients`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.totalCenter` uses this definition in the
displayed construction of `totalCenter`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValuePanel.center (s : Nat) (p : ValuePanel) : ℚ :=
  (p.domain.hi-p.domain.lo)*integralCoefficients s 0 p.coefficients
/--
Defines `ValuePanel.radius` of type `ℚ` by `(p.domain.hi-p.domain.lo)*p.error`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.totalRadius` uses this definition in the
displayed construction of `totalRadius`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValuePanel.radius (p : ValuePanel) : ℚ := (p.domain.hi-p.domain.lo)*p.error
/--
Defines `ValuePanel.box` of type `IntervalRat` by `⟨p.center s-p.radius,p.center s+p.radius,by
linarith⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.ValuePanel.integral_mem` uses this
definition to establish membership in the specified domain/enclosure: `(∫ t in
(p.domain.lo:ℝ)..p.domain.hi,f t)∈p.box s hp`.

Article: 2610.05164v2, Section 4.1.
-/
def ValuePanel.box (s : Nat) (p : ValuePanel) (hp : 0≤p.radius) : IntervalRat :=
  ⟨p.center s-p.radius,p.center s+p.radius,by linarith⟩
/--
Defines `ValuePanel.Actual` of type `Prop` by `∀ x∈Icc (0:ℝ) 1, |f
((p.domain.lo:ℝ)+((p.domain.hi:ℝ)-p.domain.lo)*x)- (exactPolynomial s p.coefficients).eval
x|≤(p.error:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.ValuePanel.integral_error` uses this
definition to prove the bound `|(∫ t in (p.domain.lo:ℝ)..p.domain.hi,f
t)-(p.center s:ℝ)|≤(p.radius:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ValuePanel.Actual (s : Nat) (p : ValuePanel) (f : ℝ → ℝ) : Prop :=
  ∀ x∈Icc (0:ℝ) 1,
    |f ((p.domain.lo:ℝ)+((p.domain.hi:ℝ)-p.domain.lo)*x)-
      (exactPolynomial s p.coefficients).eval x|≤(p.error:ℝ)

/--
The stated quantitative bound `|(∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)-(p.center
s:ℝ)|≤(p.radius:ℝ)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.ValuePanel.integral_mem` uses this bound
to establish membership in the specified domain/enclosure: `(∫ t in
(p.domain.lo:ℝ)..p.domain.hi,f t)∈p.box s hp`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error` with the arguments shown in
the proof.
-/
theorem ValuePanel.integral_error (s : Nat) (p : ValuePanel) (f : ℝ → ℝ)
    (hwidth : p.domain.lo<p.domain.hi)
    (hf : ContinuousOn f (Icc (p.domain.lo:ℝ) p.domain.hi))
    (he : p.Actual s f) :
    |(∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)-(p.center s:ℝ)|≤(p.radius:ℝ) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error` with the arguments shown
  -- in the proof.
  let w : ℝ := (p.domain.hi:ℝ)-p.domain.lo
  let a : ℝ := p.domain.lo
  have hw : 0<w := by dsimp [w]; exact_mod_cast sub_pos.mpr hwidth
  -- Establish continuity hcomp before using the function at limits or in calculus arguments.
  have hcomp : ContinuousOn (fun x => f (w*x+a)) (Icc (0:ℝ) 1) := by
    apply hf.comp (by fun_prop)
    intro x hx
    change (p.domain.lo:ℝ)≤w*x+a ∧ w*x+a≤p.domain.hi
    dsimp [a]
    constructor
    · linarith [mul_nonneg hw.le hx.1]
    · have hh := mul_le_mul_of_nonneg_left hx.2 hw.le
      dsimp [w] at hh ⊢
      linarith
  have hInt : IntervalIntegrable (fun x => f (w*x+a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hcomp
  have herror := Poly.integral_error hInt (by
    intro x hx
    simpa only [w,a,mul_comm,add_comm] using he x hx)
  have hchange := intervalIntegral.mul_integral_comp_mul_add (f := f) w a (a := (0:ℝ)) (b := 1)
  have hwa : w+a=(p.domain.hi:ℝ) := by dsimp [w,a]; ring
  simp only [mul_zero,zero_add,mul_one,hwa] at hchange
  rw [← hchange]
  change |w*(∫ x in (0:ℝ)..1,f (w*x+a))-
    (((p.domain.hi-p.domain.lo)*integralCoefficients s 0 p.coefficients:ℚ):ℝ)|≤
      (((p.domain.hi-p.domain.lo)*p.error:ℚ):ℝ)
  push_cast
  change |w*(∫ x in (0:ℝ)..1,f (w*x+a))-w*(integralCoefficients s 0 p.coefficients:ℝ)|≤w*(p.error:ℝ)
  rw [← mul_sub,abs_mul,abs_of_pos hw]
  exact mul_le_mul_of_nonneg_left herror hw.le

/--
Membership in the specified domain/enclosure: `(∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)∈p.box
s hp`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.ValuePanel.integral_error` with the arguments
shown in the proof.
-/
theorem ValuePanel.integral_mem (s : Nat) (p : ValuePanel) (f : ℝ → ℝ)
    (hwidth : p.domain.lo<p.domain.hi) (hp : 0≤p.radius)
    (hf : ContinuousOn f (Icc (p.domain.lo:ℝ) p.domain.hi))
    (he : p.Actual s f) :
    (∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)∈p.box s hp := by
  have hh := abs_le.mp (p.integral_error s f hwidth hf he)
  simp only [box,IntervalRat.mem_def,Rat.cast_sub,Rat.cast_add]
  constructor <;> linarith [hh.1,hh.2]

/--
Defines `totalCenter` of type `ℚ` by `(ps.map (ValuePanel.center s)).sum`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error_cover` rewrites with this
definition to prove the bound `|(∫ t in (a:ℝ)..b,f t)-(totalCenter s
ps:ℝ)|≤(totalRadius ps:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def totalCenter (s : Nat) (ps : List ValuePanel) : ℚ := (ps.map (ValuePanel.center s)).sum
/--
Defines `totalRadius` of type `ℚ` by `(ps.map ValuePanel.radius).sum`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error_cover` rewrites with this
definition to prove the bound `|(∫ t in (a:ℝ)..b,f t)-(totalCenter s
ps:ℝ)|≤(totalRadius ps:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def totalRadius (ps : List ValuePanel) : ℚ := (ps.map ValuePanel.radius).sum

/--
The stated quantitative bound `|(∫ t in (a:ℝ)..b,f t)-(totalCenter s ps:ℝ)|≤(totalRadius
ps:ℝ)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.amplitude_integral_error` uses this
bound to prove the bound `|(∫ q in (0:ℝ)..2,calibration.amplitude
(Real.pi^2/4) q)- (Poly.totalCenter scale quadraturePanels:ℝ)|≤(epsilon:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ps` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem integral_error_cover (s : Nat) (ps : List ValuePanel) {a b : ℚ}
    (hp : PartitionFrom a b (ps.map ValuePanel.domain)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (a:ℝ) b))
    (he : ∀ p∈ps,p.Actual s f) :
    |(∫ t in (a:ℝ)..b,f t)-(totalCenter s ps:ℝ)|≤(totalRadius ps:ℝ) := by
  -- Induct on `ps` while keeping `a` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ps generalizing a with
  | nil =>
    change a=b at hp
    subst b
    simp [totalCenter,totalRadius]
  | cons p ps ih =>
    obtain ⟨hlo,hwidth,htail⟩ := hp
    have hbound := htail.le
    have hsub : Icc (p.domain.lo:ℝ) p.domain.hi⊆Icc (a:ℝ) b :=
      Icc_subset_Icc (by exact_mod_cast hlo.ge) (by exact_mod_cast hbound)
    have hfhead := hf.mono hsub
    -- Establish continuity hftail before using the function at limits or in calculus
    -- arguments.
    have hftail : ContinuousOn f (Icc (p.domain.hi:ℝ) b) :=
      hf.mono (Icc_subset_Icc (by exact_mod_cast hlo ▸ hwidth.le) le_rfl)
    have hhead := p.integral_error s f hwidth hfhead (he p List.mem_cons_self)
    have hrest := ih htail hftail (fun q hq => he q (List.mem_cons_of_mem p hq))
    have hInt : IntervalIntegrable f volume (p.domain.lo:ℝ) p.domain.hi := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (by exact_mod_cast hwidth.le : (p.domain.lo:ℝ)≤p.domain.hi)] using hfhead
    have htInt : IntervalIntegrable f volume (p.domain.hi:ℝ) b := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (by exact_mod_cast hbound : (p.domain.hi:ℝ)≤b)] using hftail
    rw [← hlo,← intervalIntegral.integral_add_adjacent_intervals hInt htInt]
    simp only [totalCenter,totalRadius,List.map_cons,List.sum_cons,Rat.cast_add]
    have hid : (∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)+
        (∫ t in (p.domain.hi:ℝ)..b,f t)-((p.center s:ℝ)+(totalCenter s ps:ℝ))=
        ((∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)-(p.center s:ℝ))+
        ((∫ t in (p.domain.hi:ℝ)..b,f t)-(totalCenter s ps:ℝ)) := by ring
    change |((∫ t in (p.domain.lo:ℝ)..p.domain.hi,f t)+
      (∫ t in (p.domain.hi:ℝ)..b,f t))-((p.center s:ℝ)+(totalCenter s ps:ℝ))|≤
      (p.radius:ℝ)+(totalRadius ps:ℝ)
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hhead hrest)

end
end «2610.05164v2».Numerics.IntegerCertificate.Poly
