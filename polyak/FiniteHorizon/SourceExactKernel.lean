import polyak.FiniteHorizon.Noncentral
import polyak.FiniteHorizon.ExactKernel

/-!
Article: Appendix C, actual source prices and the smaller zero-price exponent.
Use: right source derivatives and the proved physical factors produce the
banded family. This exposes the actual price/kernel conclusion used in the
constant-prefactor proof rather than retaining a conditional factor premise.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality Boundary Regularity Set Filter
open scoped Topology

theorem exists_exact_price_and_kernel_decay_of_right_source_germ {q T v' : ℝ} {H : ℕ}
    (hq : 0<q) (hV : HasDerivWithinAt V v' (Ici T) T) (hv' : v'<1) (hVT : 0<V T)
    (heq : T-Real.log q=V T) (hH : 7≤H)
    (hRate : growthRate 0 (2*q) (q^2) H≤Real.exp T)
    (hfactory : ∀ᶠ t in 𝓝[≥] T,HasPhysicalFactors7 q t) :
    ∃ L : WindowPrice H,PriceNonnegative 0 (2*q) (q^2) H L ∧
      PriceContracts 0 (2*q) (q^2) H T L ∧
      (∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (multiplierMap 0 (2*q) (q^2) T) T H ν C →
        Real.exp (2*(H-5 : ℕ)*T)/2≤L (stationaryWindow ν (multiplierMap 0 (2*q) (q^2) T) C T H)) ∧
      ∃ S : ℝ,S<T ∧ ∃ C : ℝ,0<C ∧ ∀ D n : ℕ,
        ∀ s : HSegment (EuclideanSpace ℝ (Fin D)) 0 (2*q) (q^2) H n,
          H≤n → L (segmentWindow s H)=0 →
            windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H := by
  obtain ⟨a,M,δ₀,ha,hδ₀,hfamily⟩:=exists_banded_family_of_right_source_germ hq hV hv' hVT heq hH hfactory
  exact exists_exact_price_and_kernel_decay_of_banded_family (by positivity) ha hδ₀ hH hRate hfamily

/-- All source obligations are discharged on the complete noncentral regime,
including both signs and both internal source switches. -/
theorem exists_noncentral_exact_price_and_kernel_decay {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (ha : P2.Ga<Real.cosh (T q)) :
    ∃ H : ℕ,7≤H ∧ ∃ L : WindowPrice H,PriceNonnegative 0 (2*q) (q^2) H L ∧
      PriceContracts 0 (2*q) (q^2) H (T q) L ∧
      (∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (multiplierMap 0 (2*q) (q^2) (T q)) (T q) H ν C →
        Real.exp (2*(H-5 : ℕ)*T q)/2≤L (stationaryWindow ν (multiplierMap 0 (2*q) (q^2) (T q)) C (T q) H)) ∧
      ∃ S : ℝ,S<T q ∧ ∃ C : ℝ,0<C ∧ ∀ D n : ℕ,
        ∀ s : HSegment (EuclideanSpace ℝ (Fin D)) 0 (2*q) (q^2) H n,
          H≤n → L (segmentWindow s H)=0 →
            windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H := by
  obtain ⟨H,hRate,hH⟩:=((memory_rate_eq_noncentral hq hq1 ha).and (eventually_ge_atTop 7)).exists
  obtain ⟨v',hd,hv'⟩:=exists_noncentral_right_derivative ha
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  refine ⟨H,hH,?_⟩
  exact exists_exact_price_and_kernel_decay_of_right_source_germ hq hd (abs_lt.mp hv').2 hVT heq hH hRate.le
    ((eventually_hasPhysicalFactors7_of_cosh_gt_Ga hq ha).filter_mono nhdsWithin_le_nhds)

end polyak.FiniteHorizon
