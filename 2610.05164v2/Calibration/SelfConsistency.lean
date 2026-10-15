import «2610.05164v2».Calibration.CalibrationConstant
import «2610.05164v2».Calibration.Equality
import «2610.05164v2».Calibration.OneDeterminant
import «2610.05164v2».PrescribedSpeed.Congruence

/-!
Article: 2610.05164v2, Proposition 5.
Proposition 5: the self-consistent reference, coincidence with the comparison density, and
attainment of the one-determinant bound.
Result: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_minimum` supplies the stated
article conclusion.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Comparison «2610.05164v2».Filters «2610.05164v2».Continuum
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)
variable {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)

/--
Defines `SelfConsistent` of type `Prop` by `∀ q ∈ Ioo (0:ℝ) 2, R.b (Q q)*Q q=b*Q
q+R.k*ω*(R.calibration hσ hb hω).Gamma q`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_amplitude` uses this definition
to establish the identity `(R.calibration hσ hb hω).amplitude R.k q=R.amplitude q`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.
-/
def SelfConsistent : Prop := ∀ q ∈ Ioo (0:ℝ) 2,
  R.b (Q q)*Q q=b*Q q+R.k*ω*(R.calibration hσ hb hω).Gamma q

/--
Exact identity `(R.calibration hσ hb hω).amplitude R.k q=R.amplitude q`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` rewrites with this
identity to establish `(∫ x, (sqrt (R.density x))^3)= (R.calibration
hσ hb hω).base R.k (logDeterminant (kernelEigenvalue R.density_properties.1
R.density_properties.2.1) (σ*R.k))`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem selfConsistent_amplitude (hself : R.SelfConsistent hσ hb hω) {q : ℝ}
    (hq : q ∈ Icc (0:ℝ) 2) :
    (R.calibration hσ hb hω).amplitude R.k q=R.amplitude q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let C := R.calibration hσ hb hω
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · apply C.amplitude_unique R.k_positive hi (R.amplitude_positive hi)
    have he := R.amplitude_equation hq
    have hs := hself q hi
    change R.k*(R.amplitude q)^3-3*Q q*R.amplitude q-(2*b*Q q+2*R.k*ω*C.Gamma q)=0
    change R.k*(R.amplitude q)^3-3*Q q*R.amplitude q-2*R.b (Q q)*Q q=0 at he
    linarith
  · rcases Data.endpoint_cases hq hi with he | he
    · subst q
      rw [C.amplitude_zero,R.amplitude_zero]
    · subst q
      rw [C.amplitude_two,R.amplitude_two]

/--
Pointwise equality on the specified domain: `EqOn R.referenceSpeed.D ((R.calibration hσ hb
hω).comparisonSpeed R.k_positive).D (Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_coordinate` uses this pointwise
identity to establish the identity `R.referenceSpeed.X=((R.calibration hσ hb
hω).comparisonSpeed R.k_positive).X`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_eq`,
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_amplitude` with the arguments shown in
the proof.
-/
theorem selfConsistent_speed (hself : R.SelfConsistent hσ hb hω) :
    EqOn R.referenceSpeed.D ((R.calibration hσ hb hω).comparisonSpeed R.k_positive).D
      (Ioo (0:ℝ) 2) := by
  intro q hq
  change R.profile.speed q=(R.calibration hσ hb hω).speed R.k q
  rw [R.profile.speed_eq ⟨hq.1.le,hq.2.le⟩,Data.speed,R.selfConsistent_amplitude hσ hb hω hself ⟨hq.1.le,hq.2.le⟩]
  rfl

/--
Exact identity `R.density=(R.calibration hσ hb hω).comparisonDensity R.k_positive`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation` rewrites with this
identity to establish the identity `R.uncenteredDensity x=(R.calibration hσ hb
hω).comparisonDensity R.k_positive (x-R.uncenteredX 1)`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.density_congr`,
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_speed` with the arguments shown in the
proof.
-/
theorem selfConsistent_density (hself : R.SelfConsistent hσ hb hω) :
    R.density=(R.calibration hσ hb hω).comparisonDensity R.k_positive :=
  R.referenceSpeed.density_congr _ (R.selfConsistent_speed hσ hb hω hself) R.k

/--
Exact identity `R.referenceSpeed.X=((R.calibration hσ hb hω).comparisonSpeed R.k_positive).X`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 5.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_congr`,
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_speed` with the arguments shown in the
proof.
-/
theorem selfConsistent_coordinate (hself : R.SelfConsistent hσ hb hω) :
    R.referenceSpeed.X=((R.calibration hσ hb hω).comparisonSpeed R.k_positive).X :=
  R.referenceSpeed.X_congr _ (R.selfConsistent_speed hσ hb hω hself)

/--
Integrability of the displayed function: `Integrable (fun x => (sqrt (R.density x))^3)`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` uses this
integrability result to establish `(∫ x, (sqrt (R.density x))^3)=
(R.calibration hσ hb hω).base R.k (logDeterminant (kernelEigenvalue R.density_properties.1
R.density_properties.2.1) (σ*R.k))`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.density_bounded`,
`«2610.05164v2».Calibration.sqrt_cube_integrable_of_bounded`,
`«2610.05164v2».Calibration.ReferenceData.density_properties` with the arguments shown in the
proof.
-/
theorem density_energy_integrable : Integrable (fun x => (sqrt (R.density x))^3) := by
  obtain ⟨B,_,hB⟩ := R.density_bounded
  exact sqrt_cube_integrable_of_bounded R.density_properties.1 R.density_properties.2.1 hB

/--
The precise assertion is `(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)= (R.calibration
hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x)`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` rewrites with this
identity to establish `(∫ x, (sqrt (R.density x))^3)= (R.calibration
hσ hb hω).base R.k (logDeterminant (kernelEigenvalue R.density_properties.1
R.density_properties.2.1) (σ*R.k))`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Separate `x ≤ R.referenceSpeed.X 0` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem calibration_Gamma_contact {x : ℝ} :
    (R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)=
      (R.calibration hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x) := by
  -- Separate `x ≤ R.referenceSpeed.X 0` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  let C := R.calibration hσ hb hω
  by_cases hl : x ≤ R.referenceSpeed.X 0
  · rw [R.referenceSpeed.q_zero_left hl,R.contact_zero_left hσ hl,C.Gamma_zero]
    simp [Data.F]
  · by_cases hr : R.referenceSpeed.X 2 ≤ x
    · have hq := R.referenceSpeed.q_two_right hr
      have hx := R.referenceSpeed.X_endpoint_order.le.trans hr
      have hg : C.potential (R.contact hσ x)=2-R.contact hσ x := by
        rw [C.potential_eq ⟨R.contact_nonneg hσ hx,(R.contact_lt_two hσ hx).le⟩]
        exact R.potential_tail hσ ⟨R.contact_nonneg hσ hx,(R.contact_lt_two hσ hx).le⟩
          (R.contact_monotone hσ hr)
      rw [hq,C.Gamma_two,C.F_tail_value hg]
      norm_num
    · exact R.calibration_Gamma_on_support hσ hb hω ⟨(not_le.mp hl).le,(not_le.mp hr).le⟩

/--
The precise assertion is `(∫ x, (sqrt (R.density x))^3)= (R.calibration hσ hb hω).base R.k
(logDeterminant (kernelEigenvalue R.density_properties.1 R.density_properties.2.1) (σ*R.k))`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_minimum` rewrites with this
identity to prove the bound `ENNReal.ofReal (∫ x, (sqrt (R.density
x))^3) ≤ ∫⁻ x, ENNReal.ofReal (m x^(3/2:ℝ))`.

Article: 2610.05164v2, Proposition 5.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem selfConsistent_attainment (hself : R.SelfConsistent hσ hb hω)
    (hM : (∫ x, R.density x)=1) :
    (∫ x, (sqrt (R.density x))^3)=
      (R.calibration hσ hb hω).base R.k
        (logDeterminant (kernelEigenvalue R.density_properties.1 R.density_properties.2.1) (σ*R.k)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let C := R.calibration hσ hb hω
  let G := R.profile.ground R.k_positive
  have hground : groundParameter R.density_properties.1 R.density_properties.2.1=R.k := R.density_properties.2.2.2
  have hcoord : G.q=R.referenceSpeed.q := R.referenceSpeed.ground_coordinate R.k_positive G
  have hfilter : C.calibrationFilter R.density_properties.1 R.density_properties.2.1=R.filter hσ := by
    funext x
    dsimp only [Data.calibrationFilter,filter]
    rw [hground]
    rfl
  have hstate : C.calibrationState G=R.contact hσ := by
    funext x
    change G.q x-C.calibrationFilter _ _ x=R.contact hσ x
    rw [hcoord,hfilter]
    rfl
  have he := C.energy_eq_base_iff G hM R.density_energy_integrable
  rw [hground] at he
  apply he.mpr
  apply Eventually.of_forall
  intro x
  rw [hcoord,hstate]
  constructor
  · change sqrt (R.density x)=C.amplitude R.k (R.referenceSpeed.q x)
    rw [R.density_formula,sqrt_sq (R.amplitude_nonneg (R.referenceSpeed.q_mem x)),
      R.selfConsistent_amplitude hσ hb hω hself (R.referenceSpeed.q_mem x)]
  · dsimp only [Data.T]
    rw [R.calibration_Gamma_contact hσ hb hω,sub_self,mul_zero]

/--
The uncentered convention used in the article.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation` uses this definition
to establish the identity `R.uncenteredDensity x=(R.calibration hσ hb hω).comparisonDensity
R.k_positive (x-R.uncenteredX 1)`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation`.
-/
def uncenteredDensity (x : ℝ) : ℝ := R.density (x+R.referenceSpeed.X 0)
/--
Defines `uncenteredX` of type `ℝ` by `R.referenceSpeed.X q-R.referenceSpeed.X 0`.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation` uses this definition
to establish the identity `R.uncenteredDensity x=(R.calibration hσ hb hω).comparisonDensity
R.k_positive (x-R.uncenteredX 1)`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_translation`.
-/
def uncenteredX (q : ℝ) : ℝ := R.referenceSpeed.X q-R.referenceSpeed.X 0

/--
Exact identity `R.uncenteredDensity x=(R.calibration hσ hb hω).comparisonDensity R.k_positive
(x-R.uncenteredX 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 5.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.X_one`,
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_density` with the arguments shown in
the proof.
-/
theorem selfConsistent_translation (hself : R.SelfConsistent hσ hb hω) (x : ℝ) :
    R.uncenteredDensity x=(R.calibration hσ hb hω).comparisonDensity R.k_positive
      (x-R.uncenteredX 1) := by
  dsimp only [uncenteredDensity,uncenteredX]
  rw [R.X_one,R.selfConsistent_density hσ hb hω hself]
  congr 1
  ring

/--
The stated quantitative bound `(∫ x, (sqrt (R.density x))^3) ≤ ∫ x, (sqrt (m x))^3`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 5.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem selfConsistent_minimum_finite (hself : R.SelfConsistent hσ hb hω)
    (hM : (∫ x, R.density x)=1)
    {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hmass : (∫ x, m x)=1)
    (hE : Integrable (fun x => (sqrt (m x))^3)) (hk : groundParameter hm hn=R.k)
    (hH : logDeterminant (kernelEigenvalue hm hn) (σ*R.k)=
      logDeterminant (kernelEigenvalue R.density_properties.1 R.density_properties.2.1) (σ*R.k)) :
    (∫ x, (sqrt (R.density x))^3) ≤ ∫ x, (sqrt (m x))^3 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hne : ¬ m =ᵐ[volume] 0 := by
    intro he
    have hz := integral_congr_ae he
    simp only [Pi.zero_apply,integral_zero] at hz
    linarith
  let G := Classical.choice (ground_state hm hn hne)
  have h := (R.calibration hσ hb hω).energy_ge_base G hmass hE
  change (R.calibration hσ hb hω).base (groundParameter hm hn)
    (logDeterminant (kernelEigenvalue hm hn) (σ*groundParameter hm hn)) ≤ _ at h
  rw [hk,hH,← R.selfConsistent_attainment hσ hb hω hself hM] at h
  exact h

/--
Proposition 5's minimum, for the larger full L1 class and including infinite energy. The same
reference attains the bound by the preceding theorem.

The stated quantitative bound `ENNReal.ofReal (∫ x, (sqrt (R.density x))^3) ≤ ∫⁻ x,
ENNReal.ofReal (m x^(3/2:ℝ))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 5.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.one_determinant_lower_bound`,
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` with the arguments shown
in the proof.
-/
theorem selfConsistent_minimum (hself : R.SelfConsistent hσ hb hω)
    (hM : (∫ x, R.density x)=1)
    {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hmass : (∫ x, m x)=1)
    (hk : groundParameter hm hn=R.k)
    (hH : logDeterminant (kernelEigenvalue hm hn) (σ*R.k)=
      logDeterminant (kernelEigenvalue R.density_properties.1 R.density_properties.2.1) (σ*R.k)) :
    ENNReal.ofReal (∫ x, (sqrt (R.density x))^3) ≤ ∫⁻ x, ENNReal.ofReal (m x^(3/2:ℝ)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.one_determinant_lower_bound`,
  -- `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` with the arguments
  -- shown in the proof.
  have h := (R.calibration hσ hb hω).one_determinant_lower_bound hm hn hmass
  change ENNReal.ofReal ((R.calibration hσ hb hω).base (groundParameter hm hn)
    (logDeterminant (kernelEigenvalue hm hn) (σ*groundParameter hm hn))) ≤ _ at h
  rw [hk,hH,← R.selfConsistent_attainment hσ hb hω hself hM] at h
  exact h

end
end «2610.05164v2».Calibration.ReferenceData
