import chebyshev2.SineContinuum.RealLineMeasure

/-!
Article: chebyshev2, Lemma 5.
Proposition 2's unitary on the actual Lebesgue L² spaces.
Use: `chebyshev2.SineContinuum.realLineUnitary_symm_ae` feeds
`chebyshev2.SineContinuum.sineRealHilbertBasis_ae` (sine Real Hilbert Basis ae).
Proof chain: `chebyshev2.SineContinuum.green_mercer_uniform` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/--
Pullback along the actual inverse coordinate. Endpoints have zero measure.

Use: `chebyshev2.SineContinuum.realLinePullback_symm` rewrites with this definition to
establish exact identity `realLinePullback.symm f=Lp.compMeasurePreserving (fun t :
LegendreInterval => X t) X_interval_measurePreserving f`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def realLinePullback : Lp ℝ 2 realLineWeight.measure ≃ₗᵢ[ℝ] Continuum.FeatureSpace :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℝ T_interval T_interval_measurePreserving) (by
      intro f
      refine ⟨Lp.compMeasurePreserving (fun t : LegendreInterval => X t)
        X_interval_measurePreserving f,?_⟩
      change Lp.compMeasurePreserving T_interval T_interval_measurePreserving
        (Lp.compMeasurePreserving (fun t : LegendreInterval => X t)
          X_interval_measurePreserving f)=f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hi : ((fun t : LegendreInterval => X t) ∘ T_interval)=id := by
        funext x
        exact X_T x
      simp only [hi,Lp.compMeasurePreserving_id_apply])

/--
Exact identity `realLinePullback.symm f=Lp.compMeasurePreserving (fun t : LegendreInterval => X
t) X_interval_measurePreserving f`.

Use: `chebyshev2.SineContinuum.realLineUnitary_ae` rewrites with this identity to establish
exact identity `realLineUnitary f=ᵐ[volume] (fun t : LegendreInterval => f (X
t)/√(SineJacobi.phi t))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem realLinePullback_symm (f : Continuum.FeatureSpace) :
    realLinePullback.symm f=Lp.compMeasurePreserving (fun t : LegendreInterval => X t)
      X_interval_measurePreserving f := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply realLinePullback.injective
  rw [realLinePullback.apply_symm_apply]
  change f=Lp.compMeasurePreserving T_interval T_interval_measurePreserving
    (Lp.compMeasurePreserving (fun t : LegendreInterval => X t) X_interval_measurePreserving f)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hi : ((fun t : LegendreInterval => X t) ∘ T_interval)=id := funext X_T
  simp only [hi,Lp.compMeasurePreserving_id_apply]

/--
Proposition 2's unitary on the actual Lebesgue L² spaces.

Use: `chebyshev2.SineContinuum.realLineUnitary_ae` uses this definition to establish exact
identity `realLineUnitary f=ᵐ[volume] (fun t : LegendreInterval => f (X t)/√(SineJacobi.phi
t))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def realLineUnitary : Continuum.FeatureSpace ≃ₗᵢ[ℝ] LegendreSpace :=
  realLinePullback.symm.trans realLineWeight.equiv

/--
Exact identity `realLineUnitary f=ᵐ[volume] (fun t : LegendreInterval => f (X
t)/√(SineJacobi.phi t))`.

Use: `chebyshev2.SineContinuum.sineKernel_conjugacy_apply` uses this identity to establish
the precise assertion is `realLineUnitary (sineKernel f)= (2:ℝ) • greenOperator
(realLineUnitary f)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem realLineUnitary_ae (f : Continuum.FeatureSpace) :
    realLineUnitary f=ᵐ[volume] (fun t : LegendreInterval => f (X t)/√(SineJacobi.phi t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hc := realLineWeight.base_ac.ae_eq
    (Lp.coeFn_compMeasurePreserving f X_interval_measurePreserving)
  have hm := realLineWeight.mul_ae (realLinePullback.symm f)
  rw [realLinePullback_symm] at hm
  filter_upwards [hm,hc] with t hm hc
  change realLineWeight.mul (realLinePullback.symm f) t=_
  rw [realLinePullback_symm,hm,hc]
  simp only [Function.comp_def,realLineWeight,div_eq_mul_inv,mul_comm]

/--
Exact identity `realLineUnitary.symm f=ᵐ[volume] (fun x => √(SineJacobi.phi (T x))*f
(T_interval x))`.

Use: `chebyshev2.SineContinuum.sineRealHilbertBasis_ae` uses this identity to establish
exact identity `sineRealHilbertBasis j=ᵐ[volume] (fun x => √(SineJacobi.phi (T x))*upsilon j (T
x))`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem realLineUnitary_symm_ae (f : LegendreSpace) :
    realLineUnitary.symm f=ᵐ[volume] (fun x => √(SineJacobi.phi (T x))*f (T_interval x)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let g := realLineWeight.equiv.symm f
  have hg : g=ᵐ[realLineWeight.measure] (fun t => f t/realLineWeight.w t) := by
    apply realLineWeight.weight_ac.ae_eq
    have hm := realLineWeight.mul_ae g
    have he : realLineWeight.mul g=f := realLineWeight.equiv.apply_symm_apply f
    rw [he] at hm
    filter_upwards [hm,realLineWeight.nonzero] with t hm hn
    exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using hm.symm)
  have hc := T_interval_measurePreserving.quasiMeasurePreserving.ae_eq_comp hg
  have hp := Lp.coeFn_compMeasurePreserving g T_interval_measurePreserving
  filter_upwards [hp,hc] with x hp hc
  change Lp.compMeasurePreserving T_interval T_interval_measurePreserving g x=_
  rw [hp,hc]
  simp only [Function.comp_def,realLineWeight,T_interval,div_inv_eq_mul,mul_comm]

end
end chebyshev2.SineContinuum
