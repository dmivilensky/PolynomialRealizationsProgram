import polyak.FiniteHorizon.GlobalPrefactor
import polyak.FiniteHorizon.SourceExactKernel

/-!
Article: Appendix C, exact prices on every sufficiently long retained memory.
Use: the complete physical classification discharges the source factors and
right derivative at every q, including all switches and the critical point.
The smaller kernel exponent is uniform over dimensions and finite blocks.
-/
namespace polyak.FiniteHorizon
noncomputable section
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality Boundary Regularity Set Filter
open scoped Topology

/-- Genuine width-seven data with a linear positive reserve and a uniform
coefficient bound exist above the exact rate, for every retained memory H≥7. -/
theorem exists_global_above_rate_data {q : ℝ} (hq : 0<q) (hq1 : q<1)
    {H : ℕ} (hH : 7≤H) :
    ∃ a M δ₀ : ℝ,0<a ∧ 0<δ₀ ∧ ∀ δ : ℝ,0<δ → δ≤δ₀ →
      Nonempty (AboveRateData7 0 (2*q) (q^2) (T q) a M H δ) := by
  obtain ⟨v',hd,hv'⟩:=exists_global_right_derivative (T q)
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q) := by rw [←heq]; exact actual_twist_pos hq hq1
  exact exists_banded_family_of_right_source_germ hq hd (abs_lt.mp hv').2 hVT heq hH
    (Eventually.of_forall (hasPhysicalFactors7_global hq))

/-- One memory threshold suffices for actual exact-rate prices on every larger
memory. Each price is nonnegative on the genuine realizable cone, contracts on
every actual transition, is strictly positive on every finite-feasible stationary
window, and has a strictly smaller exponent uniformly on all zero-price blocks. -/
theorem exists_global_exact_price_and_kernel_decay {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ H₀ : ℕ,7≤H₀ ∧ ∀ H : ℕ,H₀≤H →
      growthRate 0 (2*q) (q^2) H=Real.exp (T q) ∧
      ∃ L : WindowPrice H,
        PriceNonnegative 0 (2*q) (q^2) H L ∧
        PriceContracts 0 (2*q) (q^2) H (T q) L ∧
        (∀ (ν : Spectrum) (C : ℝ),
          FiniteFeasible (multiplierMap 0 (2*q) (q^2) (T q)) (T q) H ν C →
            Real.exp (2*(H-5 : ℕ)*T q)/2≤
              L (stationaryWindow ν (multiplierMap 0 (2*q) (q^2) (T q)) C (T q) H)) ∧
        ∃ S : ℝ,S<T q ∧ ∃ C : ℝ,0<C ∧ ∀ D n : ℕ,
          ∀ s : HSegment (EuclideanSpace ℝ (Fin D)) 0 (2*q) (q^2) H n,
            H≤n → L (segmentWindow s H)=0 →
              windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H := by
  obtain ⟨N,hN⟩:=eventually_atTop.mp (memory_rate_eq_global hq hq1)
  refine ⟨max N 7,le_max_right _ _,fun H hH => ?_⟩
  have hH7 : 7≤H:=(le_max_right N 7).trans hH
  have hRate:=hN H ((le_max_left N 7).trans hH)
  refine ⟨hRate,?_⟩
  obtain ⟨v',hd,hv'⟩:=exists_global_right_derivative (T q)
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q) := by rw [←heq]; exact actual_twist_pos hq hq1
  exact exists_exact_price_and_kernel_decay_of_right_source_germ hq hd
    (abs_lt.mp hv').2 hVT heq hH7 hRate.le
    (Eventually.of_forall (hasPhysicalFactors7_global hq))

end
end polyak.FiniteHorizon
