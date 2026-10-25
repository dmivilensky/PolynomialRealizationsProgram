import polyak.FiniteHorizon.PricesStationary
import polyak.FiniteHorizon.SeparatedKernel

/-!
Article: Appendix C, construction and compact limit of exact-rate prices.
Use: uniformly bounded, concrete source banded data above the rate produce
actual positive contracting prices. Their coefficient subsequence retains a
strictly positive lower bound on every stationary finite-feasible window.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality Filter
open scoped Topology BigOperators

/-- Source data for the proved width-seven telescoping construction. All
coefficients and the interpolation inequality are actual, finite expressions. -/
structure AboveRateData7 (A B β T a M : ℝ) (H : ℕ) (δ : ℝ) where
  matrix : WindowMatrix7
  values : ℕ → ℝ
  factors : BandedData7 matrix values (a*δ)
  source : BandedSource7.{0} A B β (T+δ) H matrix values
  bounded : bandedSize7 matrix values+a*δ≤M

theorem exists_exact_price_of_banded_family {A B β T a M δ₀ : ℝ} {H : ℕ}
    (hB : B≠0) (ha : 0<a) (hδ₀ : 0<δ₀) (hH : 7≤H)
    (hRate : growthRate A B β H≤Real.exp T)
    (hfamily : ∀ δ : ℝ,0<δ → δ≤δ₀ → Nonempty (AboveRateData7 A B β T a M H δ)) :
    ∃ L : WindowPrice H,PriceNonnegative A B β H L ∧ PriceContracts A B β H T L ∧
      ∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (multiplierMap A B β T) T H ν C →
        Real.exp (2*(H-5 : ℕ)*T)/2≤L (stationaryWindow ν (multiplierMap A B β T) C T H) := by
  let δ : ℕ → ℝ:=fun n => δ₀/((n : ℝ)+1)
  have hδ (n : ℕ) : 0<δ n:=by dsimp [δ]; positivity
  have hδbound (n : ℕ) : δ n≤δ₀:=by
    apply (div_le_iff₀ (show (0 : ℝ)<(n : ℝ)+1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  let data : (n : ℕ) → AboveRateData7 A B β T a M H (δ n):=
    fun n => Classical.choice (hfamily (δ n) (hδ n) (hδbound n))
  let prices : ℕ → WindowPrice H:=fun n => windowPrice7 (data n).factors H a (T+δ n)
  let times : ℕ → ℝ:=fun n => T+δ n
  have hδlim : Tendsto δ atTop (𝓝 0):=by
    simpa only [δ,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul δ₀
  have htimes : Tendsto times atTop (𝓝 T):=by
    simpa only [times,add_zero] using tendsto_const_nhds.add hδlim
  have hR (n : ℕ) : growthRate A B β H<Real.exp (T+δ n):=
    hRate.trans_lt (Real.exp_lt_exp.mpr (by linarith [hδ n]))
  have hpos (n : ℕ) : PriceNonnegative A B β H (prices n):=
    windowPrice7_nonnegative (data n).factors hB ha (hδ n).le rfl hH (hR n) (data n).source
  have hstep (n : ℕ) : PriceContracts A B β H (times n) (prices n):=
    windowPrice7_contracts (data n).factors ha (hδ n).le rfl hH (data n).source
  let Mprice:=|1/a| *Real.exp (12*(|T|+δ₀))*63*M
  have hsize (n : ℕ) : priceSize (prices n)≤Mprice := by
    have hb : 0≤bandedSize7 (data n).matrix (data n).values+a*δ n:=by
      unfold bandedSize7 matrixMass7
      positivity
    have ht : |T+δ n|≤|T|+δ₀ := by
      calc
        _≤|T|+|δ n|:=abs_add_le _ _
        _=|T|+δ n:=by rw [abs_of_pos (hδ n)]
        _≤_:=by linarith [hδbound n]
    calc
      _≤|1/a| *Real.exp (12*|T+δ n|)*63*
          (bandedSize7 (data n).matrix (data n).values+a*δ n):=
        windowPrice7_size_le (data n).factors (mul_nonneg ha.le (hδ n).le) H a (T+δ n)
      _≤Mprice:=by
        dsimp [Mprice]
        have he:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤12))
        have hp:=mul_le_mul_of_nonneg_left he (abs_nonneg (1/a))
        have hp63:=mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ)≤63)
        exact mul_le_mul hp63 (data n).bounded hb (by positivity)
  let S : Set (WindowSpace H):={Y | ∃ (ν : Spectrum) (C : ℝ),
    FiniteFeasible (multiplierMap A B β T) T H ν C ∧ Y=stationaryWindow ν (multiplierMap A B β T) C T H}
  let lower : WindowSpace H → ℝ:=fun _ => Real.exp (2*(H-5 : ℕ)*T)/2
  have hlower : ∀ n,∀ Y∈S,lower Y≤prices n Y := by
    rintro n Y ⟨ν,C,hfeas,rfl⟩
    exact windowPrice7_stationary_lower (data n).factors hB ha (hδ n) rfl hH (hR n)
      (data n).source ν C hfeas
  obtain ⟨L,hLpos,hLstep,hLlower⟩:=exists_exact_price_limit prices times S lower hsize htimes hpos hstep hlower
  refine ⟨L,hLpos,hLstep,fun ν C hfeas => ?_⟩
  exact hLlower _ ⟨ν,C,hfeas,rfl⟩

theorem exists_prefactor_of_banded_family {A B β T a M δ₀ : ℝ} {H : ℕ}
    (hB : B≠0) (ha : 0<a) (hδ₀ : 0<δ₀) (hH : 7≤H)
    (hRate : growthRate A B β H≤Real.exp T)
    (hfamily : ∀ δ : ℝ,0<δ → δ≤δ₀ → Nonempty (AboveRateData7 A B β T a M H δ)) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope A B β H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨L,hpos,hstep,hlower⟩:=exists_exact_price_of_banded_family hB ha hδ₀ hH hRate hfamily
  apply exists_prefactor_of_stationary_price hB L hRate hpos hstep
  intro ν C hfeas
  exact (div_pos (Real.exp_pos _) (by norm_num : (0 : ℝ)<2)).trans_le (hlower ν C hfeas)

end polyak.FiniteHorizon
