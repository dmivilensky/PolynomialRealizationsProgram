import polyak.Duality.Certificate
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
Article: Appendix A, the finite-dimensional separation argument.
Use: prove the alternative for finitely many continuous spectral inequalities.
Proof: eliminate the single unrestricted value constant, separate the compact
convex moment image from the resulting closed cone, and recover nonnegative multipliers.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise

namespace polyak.Duality

open Spectral

/-- Article: the cone of finite slack vectors made feasible by a common value constant. -/
def valueCone {I : Type*} (σ : I → ℝ) : Set (I → ℝ) :=
  {x | ∃ C : ℝ, ∀ i, 0 ≤ x i + σ i * C}

/-- Article: one-dimensional Fourier–Motzkin elimination.
Proof: the maximum of finitely many lower bounds lies below every upper bound. -/
theorem mem_valueCone_iff {I : Type*} [Fintype I] (σ : I → ℝ)
    (p : I) (hp : 0 < σ p) (x : I → ℝ) :
    x ∈ valueCone σ ↔
      (∀ i, σ i = 0 → 0 ≤ x i) ∧
      (∀ i j, 0 < σ i → σ j < 0 → 0 ≤ (-σ j) * x i + σ i * x j) := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    constructor
    · intro i hi
      simpa [hi] using hC i
    · intro i j hi hj
      have h1 := mul_nonneg (neg_nonneg.mpr hj.le) (hC i)
      have h2 := mul_nonneg hi.le (hC j)
      nlinarith
  · rintro ⟨hzero, hpair⟩
    let P := Finset.univ.filter (fun i => 0 < σ i)
    have hP : P.Nonempty := ⟨p, by simp [P, hp]⟩
    obtain ⟨k, hk, hmax⟩ := P.exists_max_image (fun i => -x i / σ i) hP
    have hkpos : 0 < σ k := (Finset.mem_filter.mp hk).2
    refine ⟨-x k / σ k, fun i => ?_⟩
    rcases lt_trichotomy (σ i) 0 with hi | hi | hi
    · have hbound : -x k / σ k ≤ -x i / σ i := by
        apply (le_div_iff_of_neg hi).mpr
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hkpos).mpr
        nlinarith [hpair k i hkpos hi]
      have hmul := (mul_le_mul_of_nonpos_left hbound hi.le)
      rw [mul_div_cancel₀ _ (ne_of_lt hi)] at hmul
      nlinarith
    · simpa [hi] using hzero i hi
    · have hbound := hmax i (by simp [P, hi])
      have hmul := mul_le_mul_of_nonneg_left hbound hi.le
      rw [mul_div_cancel₀ _ (ne_of_gt hi)] at hmul
      nlinarith

/-- Article: closedness of the finite polyhedral cone.
Proof: Fourier–Motzkin writes it as finitely many closed halfspaces. -/
theorem isClosed_valueCone {I : Type*} [Fintype I] (σ : I → ℝ)
    (p : I) (hp : 0 < σ p) : IsClosed (valueCone σ) := by
  have heq : valueCone σ =
      {x | (∀ i, σ i = 0 → 0 ≤ x i) ∧
        (∀ i j, 0 < σ i → σ j < 0 → 0 ≤ (-σ j) * x i + σ i * x j)} := by
    ext x
    exact mem_valueCone_iff σ p hp x
  have hz : IsClosed {x : I → ℝ | ∀ i, σ i = 0 → 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_apply i)
  have hq : IsClosed {x : I → ℝ | ∀ i j, 0 < σ i → σ j < 0 →
      0 ≤ (-σ j) * x i + σ i * x j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le continuous_const
          (((continuous_apply i).const_mul _).add ((continuous_apply j).const_mul _))
  rw [heq]
  exact hz.inter hq

/-- Article: convexity of the value cone. Proof: take the same convex combination of C. -/
theorem convex_valueCone {I : Type*} (σ : I → ℝ) : Convex ℝ (valueCone σ) := by
  rintro x ⟨C, hC⟩ y ⟨D, hD⟩ u v hu hv _huv
  refine ⟨u * C + v * D, fun i => ?_⟩
  have h := add_nonneg (mul_nonneg hu (hC i)) (mul_nonneg hv (hD i))
  change 0 ≤ u * x i + v * y i + σ i * (u * C + v * D)
  nlinarith

/-- Article: convex mixture of two probability spectra.
Use: convexity of the finite moment image, without an assumed separation theorem. -/
def mixSpectrum (μ ν : Spectrum) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 1) : Spectrum :=
  ⟨ENNReal.ofReal u • (μ : Measure Frequency) + ENNReal.ofReal v • (ν : Measure Frequency),
    ⟨by simp [Measure.add_apply, Measure.smul_apply, ← ENNReal.ofReal_add hu hv, huv]⟩⟩

/-- Article: linearity of all finite moments under convex mixing. -/
theorem integral_mixSpectrum (μ ν : Spectrum) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 1) (f : C(Frequency, ℝ)) :
    (∫ c, f c ∂mixSpectrum μ ν u v hu hv huv) =
      u * (∫ c, f c ∂μ) + v * (∫ c, f c ∂ν) := by
  change (∫ c, f c ∂(ENNReal.ofReal u • (μ : Measure Frequency) +
    ENNReal.ofReal v • (ν : Measure Frequency))) = _
  rw [integral_add_measure]
  · simp [integral_smul_measure, ENNReal.toReal_ofReal hu, ENNReal.toReal_ofReal hv]
  · exact (integrable_continuous μ f.continuous).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_continuous ν f.continuous).smul_measure ENNReal.ofReal_ne_top

/-- Article: compact convex image of all probability spectra under a finite moment map. -/
def momentImage {I : Type*} (φ : I → C(Frequency, ℝ)) : Set (I → ℝ) :=
  Set.range (fun ν : Spectrum => fun i => ∫ c, φ i c ∂ν)

/-- Article: compactness of the moment image. Proof: continuous image of weakly compact spectra. -/
theorem isCompact_momentImage {I : Type*} [Fintype I] (φ : I → C(Frequency, ℝ)) :
    IsCompact (momentImage φ) :=
  isCompact_range (continuous_pi fun i => ProbabilityMeasure.continuous_integral_continuousMap (φ i))

/-- Article: convexity of the moment image. Proof: realize each convex combination by a mixture. -/
theorem convex_momentImage {I : Type*} (φ : I → C(Frequency, ℝ)) :
    Convex ℝ (momentImage φ) := by
  rintro x ⟨μ, rfl⟩ y ⟨ν, rfl⟩ u v hu hv huv
  refine ⟨mixSpectrum μ ν u v hu hv huv, ?_⟩
  funext i
  exact integral_mixSpectrum μ ν u v hu hv huv (φ i)

/-- Article: the finite strict alternative with an unrestricted common value constant.
Proof: strict Hahn–Banach separation of a compact moment image and a closed
polyhedral cone; cone rays force nonnegative coefficients and annihilate σ. -/
theorem finite_strict_alternative {I : Type*} [Fintype I]
    (φ : I → C(Frequency, ℝ)) (σ : I → ℝ) (p : I) (hp : 0 < σ p)
    (hinfeasible : ¬ ∃ (ν : Spectrum) (C : ℝ), ∀ i, 0 ≤ (∫ c, φ i c ∂ν) + σ i * C) :
    ∃ (w : I → ℝ) (ε : ℝ), (∀ i, 0 ≤ w i) ∧ 0 < ε ∧
      (∑ i, w i * σ i) = 0 ∧ ∀ c, (∑ i, w i * φ i c) ≤ -ε := by
  classical
  have hdisj : Disjoint (momentImage φ) (valueCone σ) := by
    rw [Set.disjoint_left]
    rintro x ⟨ν, rfl⟩ ⟨C, hC⟩
    exact hinfeasible ⟨ν, C, hC⟩
  obtain ⟨f, u, v, hleft, huv, hright⟩ := geometric_hahn_banach_compact_closed
    (convex_momentImage φ) (isCompact_momentImage φ)
    (convex_valueCone σ) (isClosed_valueCone σ p hp) hdisj
  have hzero : (0 : I → ℝ) ∈ valueCone σ := ⟨0, by simp⟩
  have hv : v < 0 := by simpa using hright 0 hzero
  have hnonneg (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ f x := by
    by_contra h
    have hfx : f x < 0 := lt_of_not_ge h
    obtain ⟨r, hr, hrv⟩ := exists_pos_lt_mul (neg_pos.mpr hfx) (-v)
    have hmem : r • x ∈ valueCone σ := ⟨0, fun i => by simpa using mul_nonneg hr.le (hx i)⟩
    have hsep := hright (r • x) hmem
    simp only [map_smul, smul_eq_mul] at hsep
    nlinarith
  have hline (r : ℝ) : r • σ ∈ valueCone σ :=
    ⟨-r, fun i => by change 0 ≤ r * σ i + σ i * -r; ring_nf; rfl⟩
  have hfσ : f σ = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · obtain ⟨r, _hr, hrv⟩ := exists_pos_lt_mul (neg_pos.mpr hneg) (-v)
      have hs := hright (r • σ) (hline r)
      simp only [map_smul, smul_eq_mul] at hs
      nlinarith
    · obtain ⟨r, _hr, hrv⟩ := exists_pos_lt_mul hpos (-v)
      have hs := hright ((-r) • σ) (hline (-r))
      simp only [map_smul, smul_eq_mul] at hs
      nlinarith
  let w : I → ℝ := fun i => f (Pi.single i 1)
  have hrepr (x : I → ℝ) : f x = ∑ i, w i * x i := by
    have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by ext j; simp [Pi.single_apply, mul_ite]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul, w]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨w, -u, ?_, by linarith, ?_, ?_⟩
  · intro i
    exact hnonneg _ (fun j => by simp [Pi.single_apply]; split_ifs <;> positivity)
  · rw [← hrepr, hfσ]
  · intro c
    let ν : Spectrum := ⟨Measure.dirac c, inferInstance⟩
    have hd := hleft (fun i => ∫ d, φ i d ∂ν) ⟨ν, rfl⟩
    have heq : (fun i => ∫ d, φ i d ∂ν) = fun i => φ i c := by
      funext i
      exact integral_dirac (φ i) c
    rw [heq, hrepr] at hd
    simpa using hd.le

/-- Article: the closed convex moment-plus-cone set used by finite strict separation.
Proof: a compact convex set plus a closed convex polyhedral cone is closed and convex. -/
theorem closed_convex_moment_add_cone {I : Type*} [Fintype I]
    (φ : I → C(Frequency, ℝ)) (σ : I → ℝ) (p : I) (hp : 0 < σ p) :
    IsClosed (momentImage φ + -valueCone σ) ∧ Convex ℝ (momentImage φ + -valueCone σ) :=
  ⟨(isClosed_valueCone σ p hp).neg.add_left_of_isCompact (isCompact_momentImage φ),
    (convex_momentImage φ).add (convex_valueCone σ).neg⟩

/-- Article: finite strict alternative with one additional linear spectral equality.
Use: the kernel restriction in Appendix C; the equality multiplier is unrestricted.
Proof: append the equality and its negative to the finite inequality system. -/
theorem finite_strict_alternative_equality {I : Type*} [Fintype I]
    (φ : I → C(Frequency, ℝ)) (σ : I → ℝ) (p : I) (hp : 0 < σ p)
    (e : C(Frequency, ℝ))
    (hinfeasible : ¬ ∃ (ν : Spectrum) (C : ℝ),
      (∀ i, 0 ≤ (∫ c, φ i c ∂ν) + σ i * C) ∧ (∫ c, e c ∂ν) = 0) :
    ∃ (w : I → ℝ) (θ ε : ℝ), (∀ i, 0 ≤ w i) ∧ 0 < ε ∧
      (∑ i, w i * σ i) = 0 ∧ ∀ c, (∑ i, w i * φ i c) + θ * e c ≤ -ε := by
  let φ' : I ⊕ Bool → C(Frequency, ℝ) := Sum.elim φ (fun s => if s then -e else e)
  let σ' : I ⊕ Bool → ℝ := Sum.elim σ (fun _ => 0)
  have hi : ¬ ∃ (ν : Spectrum) (C : ℝ), ∀ i, 0 ≤ (∫ c, φ' i c ∂ν) + σ' i * C := by
    rintro ⟨ν, C, h⟩
    apply hinfeasible
    refine ⟨ν, C, (fun i => h (.inl i)), ?_⟩
    have hpos := h (.inr false)
    have hneg := h (.inr true)
    simp only [φ', σ', Sum.elim_inr, Bool.false_eq_true, ↓reduceIte,
      zero_mul, add_zero, ContinuousMap.neg_apply, integral_neg] at hpos hneg
    linarith
  obtain ⟨w, ε, hw, hε, hc, hs⟩ := finite_strict_alternative φ' σ' (.inl p) hp hi
  refine ⟨fun i => w (.inl i), w (.inr false) - w (.inr true), ε,
    fun i => hw (.inl i), hε, ?_, ?_⟩
  · simpa [Fintype.sum_sum_type, σ'] using hc
  · intro c
    have h := hs c
    simp only [Fintype.sum_sum_type, Fintype.sum_bool, φ', Sum.elim_inl, Sum.elim_inr,
      ↓reduceIte, Bool.false_eq_true, ContinuousMap.neg_apply] at h
    convert h using 1
    ring

/-- Article: integration of a finite strict equality certificate excludes the primal system.
Proof: every weighted slack is nonnegative, whereas probability integration of
the pointwise symbol gives a negative value; the value and equality terms cancel. -/
theorem finite_equality_certificate_excludes {I : Type*} [Fintype I]
    (φ : I → C(Frequency, ℝ)) (σ : I → ℝ) (e : C(Frequency, ℝ))
    (w : I → ℝ) (θ ε : ℝ) (hw : ∀ i, 0 ≤ w i) (hε : 0 < ε)
    (hc : (∑ i, w i * σ i) = 0)
    (hs : ∀ c, (∑ i, w i * φ i c) + θ * e c ≤ -ε) :
    ¬ ∃ (ν : Spectrum) (C : ℝ),
      (∀ i, 0 ≤ (∫ c, φ i c ∂ν) + σ i * C) ∧ (∫ c, e c ∂ν) = 0 := by
  rintro ⟨ν, C, hp, he⟩
  have hi (i : I) : Integrable (fun c => w i * φ i c) (ν : Measure Frequency) :=
    (integrable_continuous ν (φ i).continuous).const_mul _
  have hsumint : Integrable (fun c => ∑ i, w i * φ i c) (ν : Measure Frequency) :=
    integrable_finsetSum _ fun i _ => hi i
  have heint : Integrable (fun c => θ * e c) (ν : Measure Frequency) :=
    (integrable_continuous ν e.continuous).const_mul _
  have hbound := integral_mono (hsumint.add heint) (integrable_const (-ε)) hs
  simp only [Pi.add_apply] at hbound
  rw [integral_add hsumint heint, integral_finsetSum _ (fun i _ => hi i), integral_const_mul,
    he, mul_zero, add_zero] at hbound
  simp only [integral_const_mul] at hbound
  have hnegative : (∑ i, w i * (∫ c, φ i c ∂ν)) ≤ -ε := by simpa using hbound
  have hpositive : 0 ≤ ∑ i, w i * ((∫ c, φ i c ∂ν) + σ i * C) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hp i)
  have hcancel : (∑ i, w i * ((∫ c, φ i c ∂ν) + σ i * C)) =
      ∑ i, w i * (∫ c, φ i c ∂ν) := by
    simp_rw [mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hc, zero_mul, add_zero]
  rw [hcancel] at hpositive
  linarith

end polyak.Duality
