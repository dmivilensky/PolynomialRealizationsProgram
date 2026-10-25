import chebyshev2.SineContinuum.MercerBasis
import chebyshev2.SineContinuum.GreenInverse

/-!
Article: chebyshev2, Lemma 5.
Mercer Expansion.
Use: `chebyshev2.SineContinuum.green_mercer_hasSum` feeds
`chebyshev2.SineContinuum.green_mercer_closed` (green mercer closed).
Proof chain: `chebyshev2.SineContinuum.green_mercer_uniform` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion. The needed form is
proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
open scoped InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency true

/--
Exact identity `sineRealHilbertBasis j=ᵐ[volume] (fun x => √(SineJacobi.phi (T x))*upsilon j (T
x))`.

Use: `chebyshev2.SineContinuum.mercerVector_coefficient` uses this identity to establish
the precise assertion is `inner ℝ (mercerVector j) (sineFeature t)=
√(Continuum.referenceEigenvalue j)*upsilon j t`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineRealHilbertBasis_ae (j : ℕ) : sineRealHilbertBasis j=ᵐ[volume]
    (fun x => √(SineJacobi.phi (T x))*upsilon j (T x)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have ht := T_interval_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (realLineWeight.weight_ac.ae_eq (sineHilbertBasis_ae j))
  rw [sineRealHilbertBasis_apply]
  filter_upwards [realLineUnitary_symm_ae (sineHilbertBasis j),ht] with x hu ht
  simp only [Function.comp_def] at ht
  rw [hu,ht]
  rfl

/--
The precise assertion is `inner ℝ (mercerVector j) (sineFeature t)=
√(Continuum.referenceEigenvalue j)*upsilon j t`.

Use: `chebyshev2.SineContinuum.green_mercer_hasSum` rewrites with this identity to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu
j) (green t s)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem mercerVector_coefficient (j : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    inner ℝ (mercerVector j) (sineFeature t)=
      √(Continuum.referenceEigenvalue j)*upsilon j t := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have he := sineEvaluation_mercerVector j
  have ha : Continuum.rawEvaluation m (mercerVector j)=ᵐ[volume]
      (fun x => √(Continuum.referenceEigenvalue j)*√(SineJacobi.phi (T x))*upsilon j (T x)) := by
    have hv := Continuum.evaluationOperator_coe m_integrable (fun x => (m_positive x).le) (mercerVector j)
    change sineEvaluation (mercerVector j)=ᵐ[volume] _ at hv
    rw [he] at hv
    filter_upwards [hv,Lp.coeFn_smul √(Continuum.referenceEigenvalue j) (sineRealHilbertBasis j),
      sineRealHilbertBasis_ae j] with x hv hs hb
    rw [← hv,hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hb]
    ring
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (Continuum.rawEvaluation m (mercerVector j)) :=
    m_continuous.sqrt.mul (Continuum.feature_continuous.inner continuous_const)
  -- Establish continuity hd before using the function at limits or in calculus arguments.
  have hd : Continuous (fun x => √(Continuum.referenceEigenvalue j)*
      √(SineJacobi.phi (T x))*upsilon j (T x)) :=
    (continuous_const.mul n_continuous.sqrt).mul ((upsilon_continuous j).comp T_continuous)
  have h := congrFun ((hc.ae_eq_iff_eq volume hd).mp ha) (X t)
  simp only [Continuum.rawEvaluation,sqrt_m,n_X ht,T_X ht] at h
  rw [real_inner_comm (sineFeature t) (mercerVector j),sineFeature,real_inner_smul_left]
  have hp := SineJacobi.phi_pos ht
  apply mul_left_cancel₀ (sqrt_pos.mpr hp).ne'
  calc
    _ = SineJacobi.phi t*inner ℝ (Continuum.feature (X t)) (mercerVector j) := by
      rw [← mul_assoc,← pow_two,sq_sqrt hp.le]
    _ = _ := by rw [h]; ring

/--
The value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu j) (green
t s)`.

Use: `chebyshev2.SineContinuum.green_mercer_diagonal` uses this infinite-sum formula to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t^2/mu j)
((1/2)*SineJacobi.phi t)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_mercer_hasSum {t s : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hs : s ∈ Ioo (0:ℝ) 1) :
    HasSum (fun j => upsilon j t*upsilon j s/mu j) (green t s) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h := (mercerHilbertBasis.hasSum_repr (sineFeature t)).mapL (innerSL ℝ (sineFeature s))
  have he (j : ℕ) : inner ℝ (sineFeature s)
      (mercerHilbertBasis.repr (sineFeature t) j • mercerHilbertBasis j)=
      2*(upsilon j t*upsilon j s/mu j) := by
    rw [mercerHilbertBasis.repr_apply_apply,mercerHilbertBasis_apply,
      real_inner_smul_right,mercerVector_coefficient j ht,
      real_inner_comm (mercerVector j) (sineFeature s),mercerVector_coefficient j hs]
    have hsq := sq_sqrt (Continuum.referenceEigenvalue_pos j).le
    have hm := mu_reference j
    rw [div_eq_mul_inv]
    calc
      _ = (√(Continuum.referenceEigenvalue j))^2*(upsilon j t*upsilon j s) := by ring
      _ = _ := by rw [hsq,hm]; ring
  change HasSum (fun j => inner ℝ (sineFeature s)
    (mercerHilbertBasis.repr (sineFeature t) j • mercerHilbertBasis j))
      (inner ℝ (sineFeature s) (sineFeature t)) at h
  simp only [he,sineFeature_inner hs ht] at h
  have hg : green s t=green t s := by simp only [green,min_comm s t,max_comm s t]
  rw [hg] at h
  convert h.mul_left (1/2:ℝ) using 1
  · funext j; ring
  · ring

/--
The value of a convergent infinite sum: `HasSum (fun j => upsilon j t^2/mu j)
((1/2)*SineJacobi.phi t)`.

Use: a standalone supporting infinite-sum formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_mercer_diagonal {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasSum (fun j => upsilon j t^2/mu j) ((1/2)*SineJacobi.phi t) := by
  have h := green_mercer_hasSum ht ht
  convert h using 1
  · funext j; ring
  · have hg := green_diagonal t
    linarith

end
end chebyshev2.SineContinuum
