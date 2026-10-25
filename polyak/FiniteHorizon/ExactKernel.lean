import polyak.FiniteHorizon.KernelDecay
import polyak.FiniteHorizon.ExactPrices

/-!
Article: Appendix C, exact price and smaller rate on its kernel.
Use: the actual source banded family produces the price and its positive
stationary reserve; separation and finite-block continuation then yield a
uniform smaller exponent for every actual zero-price segment.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality

theorem exists_exact_price_and_kernel_decay_of_banded_family {A B β T a M δ₀ : ℝ} {H : ℕ}
    (hB : B≠0) (ha : 0<a) (hδ₀ : 0<δ₀) (hH : 7≤H)
    (hRate : growthRate A B β H≤Real.exp T)
    (hfamily : ∀ δ : ℝ,0<δ → δ≤δ₀ → Nonempty (AboveRateData7 A B β T a M H δ)) :
    ∃ L : WindowPrice H,PriceNonnegative A B β H L ∧ PriceContracts A B β H T L ∧
      (∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (multiplierMap A B β T) T H ν C →
        Real.exp (2*(H-5 : ℕ)*T)/2≤L (stationaryWindow ν (multiplierMap A B β T) C T H)) ∧
      ∃ S : ℝ,S<T ∧ ∃ C : ℝ,0<C ∧ ∀ D n : ℕ,
        ∀ s : HSegment (EuclideanSpace ℝ (Fin D)) A B β H n,H≤n → L (segmentWindow s H)=0 →
          windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H := by
  obtain ⟨L,hpos,hstep,hlower⟩:=exists_exact_price_of_banded_family hB ha hδ₀ hH hRate hfamily
  refine ⟨L,hpos,hstep,hlower,?_⟩
  apply exists_kernel_segment_decay_of_stationary_price hB L hRate hpos hstep
  intro ν C hfeas
  exact (div_pos (Real.exp_pos _) (by norm_num : (0 : ℝ)<2)).trans_le (hlower ν C hfeas)

end polyak.FiniteHorizon
