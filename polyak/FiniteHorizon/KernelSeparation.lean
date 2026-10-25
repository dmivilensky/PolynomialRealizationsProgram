import polyak.FiniteHorizon.StationaryWindow
import polyak.Duality.Equality
import polyak.Duality.Separation

/-!
Article: Appendix C, strict separation on the invariant zero-price kernel.
Use: a price positive on every stationary feasible pair excludes that pair
from its kernel. Separation retains the actual affine coefficient of C.
-/
noncomputable section
namespace polyak.FiniteHorizon
open MeasureTheory Spectral Duality Growth.FiniteHorizon
open scoped BigOperators

theorem stationary_kernel_separation {H : ℕ} (L : WindowSpace H →L[ℝ] ℝ)
    (m : C(Frequency,ℂ)) (t : ℝ)
    (hpos : ∀ (ν : Spectrum) (C : ℝ), FiniteFeasible m t H ν C →
      0<L (stationaryWindow ν m C t H)) :
    ∃ (w : ConstraintIndex (Finset.Icc 1 H) → ℝ) (ζ ε : ℝ),
      (∀ i,0≤w i) ∧ 0<ε ∧
      ((∑ n∈Finset.Icc 1 H,
        (lagWeight (Finset.Icc 1 H) w false n-lagWeight (Finset.Icc 1 H) w true n)*
          Real.sinh (n*t))+w (.inl false)-w (.inl true))+
        ζ*stationaryPriceCharge L t=0 ∧
      ∀ c, symbol m t (Finset.Icc 1 H)
        (lagWeight (Finset.Icc 1 H) w false) (lagWeight (Finset.Icc 1 H) w true)
        (w (.inl false)) (w (.inl true)) c+
          ζ*stationaryPriceIntegrand L m t c≤ -ε := by
  have hi : ¬ ∃ (ν : Spectrum) (C : ℝ),
      (∀ i : ConstraintIndex (Finset.Icc 1 H),
        0≤(∫ c,constraintMap m t (Finset.Icc 1 H) i c ∂ν)+
          constraintCharge t (Finset.Icc 1 H) i*C) ∧
        (∫ c,stationaryPriceIntegrand L m t c ∂ν)+stationaryPriceCharge L t*C=0 := by
    rintro ⟨ν,C,h,hzero⟩
    have hp := hpos ν C ((finite_constraints_iff m t H ν C).mp h)
    rw [price_stationaryWindow_eq] at hp
    linarith
  obtain ⟨w,ζ,ε,hw,hε,hc,hs⟩ := finite_strict_alternative_affine_equality
    (constraintMap m t (Finset.Icc 1 H)) (constraintCharge t (Finset.Icc 1 H))
    (.inl false) (by norm_num [constraintCharge])
    (stationaryPriceIntegrand L m t) (stationaryPriceCharge L t) hi
  refine ⟨w,ζ,ε,hw,hε,?_,?_⟩
  · rwa [sum_constraintCharge] at hc
  · intro c
    simpa only [sum_constraintMap] using hs c

end polyak.FiniteHorizon
