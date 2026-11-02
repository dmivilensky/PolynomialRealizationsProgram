import krylov.Strings.GeneralSpectralMeasure
import krylov.Strings.GeneralSpectralWeylLower
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: main_krylov, apC:prop:tauber, local upper Weyl comparison.
Use: genuine compactly supported exponential trials in the physical energy
space. Only an upper density bound on one initial interval is needed.
Source: the Dirichlet variational principle and elementary exponential
integration; no global mass bound or spectral asymptotic is assumed.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory Real
open scoped Topology

/-- Normalization of the exponentially decaying compact physical trial. -/
def trialDenominator (δ k : ℝ) : ℝ := 1 - Real.exp (-k * δ)

theorem trialDenominator_pos {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    0 < trialDenominator δ k := by
  unfold trialDenominator
  have he : Real.exp (-k * δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- Smooth profile on the initial interval, with values one and zero at
its two endpoints. The physical trial is its compact truncation. -/
def trialProfile (δ k x : ℝ) : ℝ :=
  (Real.exp (-k * x) - Real.exp (-k * δ)) / trialDenominator δ k

/-- The true derivative of the untruncated exponential profile. -/
def trialDerivative (δ k x : ℝ) : ℝ :=
  -k * Real.exp (-k * x) / trialDenominator δ k

theorem trialProfile_hasDerivAt (δ k x : ℝ) :
    HasDerivAt (trialProfile δ k) (trialDerivative δ k x) x := by
  change HasDerivAt (fun y ↦ (Real.exp (-k * y) - Real.exp (-k * δ)) / trialDenominator δ k)
    (-k * Real.exp (-k * x) / trialDenominator δ k) x
  simpa only [id_eq, mul_one, mul_comm] using
    (((hasDerivAt_id x).const_mul (-k)).exp.sub_const
      (Real.exp (-k * δ))).div_const (trialDenominator δ k)

theorem trialProfile_zero {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    trialProfile δ k 0 = 1 := by
  simp only [trialProfile, mul_zero, Real.exp_zero]
  exact div_self (trialDenominator_pos hδ hk).ne'

theorem trialProfile_endpoint (δ k : ℝ) : trialProfile δ k δ = 0 := by
  simp [trialProfile]

/-- The compact trial is nonnegative and lies below the normalized pure
exponential. This comparison retains the sharp leading coefficient. -/
theorem trialProfile_bounds {δ k x : ℝ} (hδ : 0 < δ) (hk : 0 < k)
    (hx : x ∈ Icc 0 δ) :
    0 ≤ trialProfile δ k x ∧
      trialProfile δ k x ≤ Real.exp (-k * x) / trialDenominator δ k := by
  have hd := trialDenominator_pos hδ hk
  constructor
  · apply div_nonneg _ hd.le
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [hx.2]))
  · exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hd.le

/-- Elementary exponential square integral, used for both mass and gradient
energy of the same actual compact trial. -/
theorem exponential_square_integral_le {δ k : ℝ} (hδ : 0 ≤ δ) (hk : 0 < k) :
    (∫ x in Ioc 0 δ, Real.exp (-k * x) ^ 2) ≤ 1 / (2 * k) := by
  have hd (x : ℝ) : HasDerivAt (fun y ↦ -Real.exp (-2 * k * y) / (2 * k))
      (Real.exp (-2 * k * x)) x := by
    convert (((hasDerivAt_id x).const_mul (-2 * k)).exp.neg.div_const (2 * k)) using 1
    · rfl
    · dsimp
      field_simp
  have he : (∫ x in (0 : ℝ)..δ, Real.exp (-2 * k * x)) =
      (1 - Real.exp (-2 * k * δ)) / (2 * k) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hd x) ((by fun_prop : Continuous (fun x : ℝ ↦ Real.exp (-2 * k * x))).intervalIntegrable _ _)]
    simp only [mul_zero, Real.exp_zero]
    ring
  have hs (x : ℝ) : Real.exp (-k * x) ^ 2 = Real.exp (-2 * k * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hs]
  rw [← intervalIntegral.integral_of_le hδ, he]
  exact div_le_div_of_nonneg_right
    (sub_le_self 1 (Real.exp_pos _).le) (by positivity)

/-- The literal compactly supported physical mass representative. -/
def exponentialTrial (δ k : ℝ) : ℝ → ℂ :=
  (Icc 0 δ).indicator (fun x ↦ (trialProfile δ k x : ℂ))

/-- Its literal physical weak derivative, with no endpoint atom. -/
def exponentialTrialDerivative (δ k : ℝ) : ℝ → ℂ :=
  (Ioc 0 δ).indicator (fun x ↦ (trialDerivative δ k x : ℂ))

private theorem trialProfile_continuous (δ k : ℝ) : Continuous (trialProfile δ k) :=
  continuous_iff_continuousAt.mpr fun x ↦ (trialProfile_hasDerivAt δ k x).continuousAt

/-- The compact profile has genuine mass L² regularity whenever its
support has finite mass; no finiteness outside that support is needed. -/
theorem exponentialTrial_memLp (μ : Measure ℝ) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hf : μ (Icc 0 δ) ≠ ⊤) :
    MemLp (exponentialTrial δ k) 2 μ := by
  have hi := memLp_indicator_const (μ := μ) 2 measurableSet_Icc
    ((1 / trialDenominator δ k : ℝ) : ℂ) (Or.inr hf)
  apply hi.of_le ((Complex.continuous_ofReal.comp (trialProfile_continuous δ k)).aestronglyMeasurable.indicator measurableSet_Icc)
  filter_upwards [] with x
  change ‖(Icc 0 δ).indicator (fun x ↦ (trialProfile δ k x : ℂ)) x‖ ≤
    ‖(Icc 0 δ).indicator (fun _ ↦ ((1 / trialDenominator δ k : ℝ) : ℂ)) x‖
  by_cases hx : x ∈ Icc 0 δ
  · simp only [indicator_of_mem hx, Complex.norm_real,
      Real.norm_of_nonneg (trialProfile_bounds hδ hk hx).1,
      Real.norm_of_nonneg (one_div_nonneg.mpr (trialDenominator_pos hδ hk).le)]
    exact (trialProfile_bounds hδ hk hx).2.trans
      (div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith [hx.1]))
        (trialDenominator_pos hδ hk).le)
  · simp only [indicator_of_notMem hx, norm_zero, le_refl]

/-- The actual compact profile as a mass-Hilbert vector. -/
def exponentialTrialVector (S : StringMeasure) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hf : S.measure (Icc 0 δ) ≠ ⊤) : MassHilbert S.measure :=
  (exponentialTrial_memLp S.measure hδ hk hf).toLp (exponentialTrial δ k)

theorem exponentialTrialVector_ae (S : StringMeasure) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hf : S.measure (Icc 0 δ) ≠ ⊤) :
    exponentialTrialVector S hδ hk hf =ᵐ[S.measure] exponentialTrial δ k := MemLp.coeFn_toLp _

/-- The true compact trial has boundary value one at the distinguished
physical unit atom. -/
theorem exponentialTrialVector_trace (S : StringMeasure) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hf : S.measure (Icc 0 δ) ≠ ⊤) :
    boundaryTrace S (exponentialTrialVector S hδ hk hf) = 1 := by
  rw [boundaryTrace_apply, eq_at_origin_of_ae_eq S (exponentialTrialVector_ae S hδ hk hf)]
  simp [exponentialTrial, hδ.le, trialProfile_zero hδ hk]

/-- The derivative is genuinely square integrable in the physical
Lebesgue-gradient space and has compact support. -/
theorem exponentialTrialDerivative_memLp {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    MemLp (exponentialTrialDerivative δ k) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hf : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 δ) ≠ ⊤ := by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    simp
  have hi := memLp_indicator_const (μ := volume.restrict (Ioi (0 : ℝ))) 2 measurableSet_Ioc
    ((k / trialDenominator δ k : ℝ) : ℂ) (Or.inr hf)
  have hc : Continuous (fun x ↦ (trialDerivative δ k x : ℂ)) := by
    unfold trialDerivative
    fun_prop
  apply hi.of_le (hc.aestronglyMeasurable.indicator measurableSet_Ioc)
  filter_upwards [] with x
  change ‖(Ioc 0 δ).indicator (fun x ↦ (trialDerivative δ k x : ℂ)) x‖ ≤
    ‖(Ioc 0 δ).indicator (fun _ ↦ ((k / trialDenominator δ k : ℝ) : ℂ)) x‖
  by_cases hx : x ∈ Ioc 0 δ
  · simp only [indicator_of_mem hx, Complex.norm_real, trialDerivative,
      norm_div, norm_neg, Real.norm_of_nonneg hk.le,
      Real.norm_of_nonneg (trialDenominator_pos hδ hk).le, norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply div_le_div_of_nonneg_right _ (trialDenominator_pos hδ hk).le
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by nlinarith [hx.1])) hk.le).trans_eq (mul_one k)
  · simp only [indicator_of_notMem hx, norm_zero, le_refl]

/-- The true derivative as an actual physical gradient vector. -/
def exponentialTrialGradient {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) : GradientHilbert :=
  (exponentialTrialDerivative_memLp hδ hk).toLp (exponentialTrialDerivative δ k)

theorem exponentialTrialGradient_ae {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    exponentialTrialGradient hδ hk =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      exponentialTrialDerivative δ k := MemLp.coeFn_toLp _

private theorem derivative_integral (δ k a b : ℝ) :
    (∫ x in a..b, (trialDerivative δ k x : ℂ)) =
      (trialProfile δ k b : ℂ) - (trialProfile δ k a : ℂ) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact (trialProfile_hasDerivAt δ k x).ofReal_comp
  · have hc : Continuous (fun x ↦ (trialDerivative δ k x : ℂ)) := by
      unfold trialDerivative
      fun_prop
    exact hc.intervalIntegrable _ _

/-- The actual gradient primitive equals the compact exponential profile
minus its boundary value on the whole physical half-line. -/
theorem exponentialTrialGradient_primitive {δ k x : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hx : 0 ≤ x) :
    1 + Spectral.gradientPrimitive (exponentialTrialGradient hδ hk) x =
      exponentialTrial δ k x := by
  rw [Spectral.gradientPrimitive_eq_setIntegral _ hx]
  have he : (∫ y in Ioc 0 x, exponentialTrialGradient hδ hk y
      ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫ y in Ioc 0 (min δ x), (trialDerivative δ k y : ℂ) := by
    rw [setIntegral_congr_ae measurableSet_Ioc
      ((exponentialTrialGradient_ae hδ hk).mono fun _ he _ ↦ he)]
    unfold exponentialTrialDerivative
    have hs : Ioc (0 : ℝ) δ ∩ Ioc 0 x = Ioc 0 (min δ x) := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, le_min_iff]
      tauto
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, hs,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self]
  rw [he, ← intervalIntegral.integral_of_le (le_min hδ.le hx), derivative_integral,
    trialProfile_zero hδ hk, Complex.ofReal_one]
  by_cases hxd : x ≤ δ
  · rw [min_eq_right hxd, exponentialTrial,
      indicator_of_mem (show x ∈ Icc 0 δ from ⟨hx, hxd⟩)]
    ring
  · rw [min_eq_left (le_of_not_ge hxd), trialProfile_endpoint, Complex.ofReal_zero]
    simp [exponentialTrial, hxd]

/-- The compact exponential pair belongs to the actual physical energy
graph. This is proved from its genuine derivative and actual mass vector. -/
theorem exponentialTrial_mem_energyGraph (S : StringMeasure) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) :
    WithLp.toLp 2 (exponentialTrialVector S hδ hk hf, exponentialTrialGradient hδ hk) ∈ energyGraph S := by
  apply energyGraph_mem_of_ae
  have hn : ∀ᵐ x ∂(S.measure), 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le, Iio] using hphysical
  filter_upwards [exponentialTrialVector_ae S hδ hk hf, hn] with x he hx
  rw [exponentialTrialVector_trace S hδ hk hf, he]
  exact (exponentialTrialGradient_primitive hδ hk hx).symm

/-- The local mass integral of the real trial has the sharp exponential
upper coefficient. -/
theorem trialProfile_sq_integral_le {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    (∫ x in Ioc 0 δ, trialProfile δ k x ^ 2) ≤
      1 / (2 * k * trialDenominator δ k ^ 2) := by
  have hi := (trialProfile_continuous δ k).pow 2
  have he : Continuous (fun x : ℝ ↦ Real.exp (-k * x) ^ 2 / trialDenominator δ k ^ 2) := by fun_prop
  have hb : (∫ x in Ioc 0 δ, trialProfile δ k x ^ 2) ≤
      ∫ x in Ioc 0 δ, Real.exp (-k * x) ^ 2 / trialDenominator δ k ^ 2 := by
    rw [← intervalIntegral.integral_of_le hδ.le, ← intervalIntegral.integral_of_le hδ.le]
    apply intervalIntegral.integral_mono_on hδ.le (hi.intervalIntegrable _ _) (he.intervalIntegrable _ _)
    intro x hx
    have ht := trialProfile_bounds hδ hk hx
    calc
      _ ≤ (Real.exp (-k * x) / trialDenominator δ k) ^ 2 :=
        sq_le_sq₀ ht.1 (div_nonneg (Real.exp_pos _).le (trialDenominator_pos hδ hk).le) |>.mpr ht.2
      _ = _ := div_pow _ _ _
  rw [integral_div] at hb
  have hd : 0 < trialDenominator δ k ^ 2 := sq_pos_of_pos (trialDenominator_pos hδ hk)
  exact hb.trans ((div_le_div_of_nonneg_right (exponential_square_integral_le hδ.le hk) hd.le).trans_eq (by ring))

/-- The actual physical gradient norm is bounded with the matching sharp
half coefficient. -/
theorem exponentialTrialGradient_norm_sq_le {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    ‖exponentialTrialGradient hδ hk‖ ^ 2 ≤ k / (2 * trialDenominator δ k ^ 2) := by
  rw [← integral_norm_sq_eq]
  rw [integral_congr_ae ((exponentialTrialGradient_ae hδ hk).mono
    fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx)]
  have hf : (fun x ↦ ‖exponentialTrialDerivative δ k x‖ ^ 2) =
      (Ioc 0 δ).indicator (fun x ↦ k ^ 2 * Real.exp (-k * x) ^ 2 / trialDenominator δ k ^ 2) := by
    ext x
    by_cases hx : x ∈ Ioc 0 δ
    · simp only [exponentialTrialDerivative, indicator_of_mem hx, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, trialDerivative, div_pow, mul_pow, neg_sq]
    · simp only [exponentialTrialDerivative, indicator_of_notMem hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [hf, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    integral_div, integral_const_mul]
  have he := mul_le_mul_of_nonneg_left (exponential_square_integral_le hδ.le hk) (sq_nonneg k)
  have hd : 0 < trialDenominator δ k ^ 2 := sq_pos_of_pos (trialDenominator_pos hδ hk)
  exact (div_le_div_of_nonneg_right he hd.le).trans_eq (by field_simp)

/-- The actual mass vector has only the unit atom and a controlled local
density contribution. Arbitrary remote mass plays no role. -/
theorem exponentialTrialVector_norm_sq_le (S : StringMeasure) {δ k ρ : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hρ : 0 ≤ ρ) (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hupper : S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    ‖exponentialTrialVector S hδ hk hf‖ ^ 2 ≤
      1 + ρ / (2 * k * trialDenominator δ k ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ trialProfile δ k x ^ 2
  have hi : IntegrableOn f (Icc 0 δ) S.measure := by
    have hh := (exponentialTrial_memLp S.measure hδ hk hf).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    apply hh.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [exponentialTrial, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, sq_abs, f]
  have he : ‖exponentialTrialVector S hδ hk hf‖ ^ 2 =
      1 + ∫ x in Ioc 0 δ, f x ∂S.measure := by
    rw [← integral_norm_sq_eq, integral_congr_ae ((exponentialTrialVector_ae S hδ hk hf).mono
      fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx)]
    have hfun : (fun x ↦ ‖exponentialTrial δ k x‖ ^ 2) = (Icc 0 δ).indicator f := by
      ext x
      by_cases hx : x ∈ Icc 0 δ
      · simp only [exponentialTrial, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, sq_abs, f]
      · simp only [exponentialTrial, indicator_of_notMem hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hs : Icc (0 : ℝ) δ = {0} ∪ Ioc 0 δ := by
      ext x
      simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨hx, hxd⟩
        exact (eq_or_lt_of_le hx).elim (fun he ↦ Or.inl he.symm) (fun hp ↦ Or.inr ⟨hp, hxd⟩)
      · rintro (rfl | ⟨hx, hxd⟩)
        · exact ⟨le_rfl, hδ.le⟩
        · exact ⟨hx.le, hxd⟩
    rw [hfun, integral_indicator measurableSet_Icc, hs,
      setIntegral_union (by simp : Disjoint ({0} : Set ℝ) (Ioc 0 δ)) measurableSet_Ioc
        (hi.mono_set (by rw [hs]; exact subset_union_left))
        (hi.mono_set (by rw [hs]; exact subset_union_right)),
      integral_singleton, Measure.real, S.origin, ENNReal.toReal_one, one_smul]
    simp only [f, trialProfile_zero hδ hk, one_pow]
  have hc : Continuous f := (trialProfile_continuous δ k).pow 2
  have hiv : Integrable f (ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :=
    (hc.intervalIntegrable 0 δ).1.smul_measure (by simp)
  have hm := integral_mono_measure hupper (Filter.Eventually.of_forall fun x ↦ sq_nonneg (trialProfile δ k x)) hiv
  rw [integral_smul_measure, ENNReal.toReal_ofReal hρ, smul_eq_mul] at hm
  rw [he]
  have hb := mul_le_mul_of_nonneg_left (trialProfile_sq_integral_le hδ hk) hρ
  rw [mul_one_div] at hb
  change ρ * (∫ x in Ioc 0 δ, f x) ≤ _ at hb
  linarith

/-- A genuine physical unit-trace test attains the sharp leading upper
Weyl energy. Every vector, derivative and energy bound is constructed from
the actual local density domination. -/
theorem exists_exponential_trial (S : StringMeasure) {δ ρ t : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (ht : 0 < t)
    (hf : S.measure (Icc 0 δ) ≠ ⊤) (hphysical : S.measure (Iio 0) = 0)
    (hupper : S.measure.restrict (Ioc 0 δ) ≤ ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ)) :
    ∃ w : EnergyAmbient S.measure, w ∈ energyGraph S ∧ boundaryTrace S w.fst = 1 ∧
      t * ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 ≤
        t + sqrt (t * ρ) / trialDenominator δ (sqrt (t * ρ)) ^ 2 := by
  let k := sqrt (t * ρ)
  have hk : 0 < k := sqrt_pos.mpr (mul_pos ht hρ)
  refine ⟨WithLp.toLp 2 (exponentialTrialVector S hδ hk hf, exponentialTrialGradient hδ hk),
    exponentialTrial_mem_energyGraph S hδ hk hf hphysical,
    exponentialTrialVector_trace S hδ hk hf, ?_⟩
  change t * ‖exponentialTrialVector S hδ hk hf‖ ^ 2 + ‖exponentialTrialGradient hδ hk‖ ^ 2 ≤ _
  have hm := mul_le_mul_of_nonneg_left
    (exponentialTrialVector_norm_sq_le S hδ hk hρ.le hf hupper) ht.le
  have hg := exponentialTrialGradient_norm_sq_le hδ hk
  have he : t * (1 + ρ / (2 * k * trialDenominator δ k ^ 2)) +
      k / (2 * trialDenominator δ k ^ 2) = t + k / trialDenominator δ k ^ 2 := by
    have hs : k ^ 2 = t * ρ := sq_sqrt (mul_pos ht hρ).le
    field_simp [hk.ne', (trialDenominator_pos hδ hk).ne']
    nlinarith
  exact (add_le_add hm hg).trans_eq he

end
end krylov.Strings.GeneralSpectral
