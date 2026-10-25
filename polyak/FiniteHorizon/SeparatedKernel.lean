import polyak.FiniteHorizon.StationaryKernel
import polyak.FiniteHorizon.KernelSeparation
import polyak.FiniteHorizon.KernelBound

/-!
Article: Appendix C, concrete separated kernel and the uniform prefactor.
Use: affine separation supplies raw nonnegative interpolation weights; adding
the actual price cancels their common value charge and leaves a strictly
negative finite kernel on the entire Fourier circle.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Duality
open scoped BigOperators

def separationCombination (t : ℝ) (H : ℕ)
    (w : ConstraintIndex (Finset.Icc 1 H) → ℝ) (hw : ∀ i,0≤w i) : FiniteCombination t where
  lags:=Finset.Icc 1 H
  positive_lag n hn:=(Finset.mem_Icc.mp hn).1
  α:=lagWeight (Finset.Icc 1 H) w false
  β:=lagWeight (Finset.Icc 1 H) w true
  α_nonneg n hn:=by simp only [lagWeight,dite_eq_left hn]; exact hw _
  β_nonneg n hn:=by simp only [lagWeight,dite_eq_left hn]; exact hw _
  γplus:=w (.inl false)
  γminus:=w (.inl true)
  γplus_nonneg:=hw _
  γminus_nonneg:=hw _

def separatedKernel {H : ℕ} (L : WindowPrice H) (A B β t : ℝ)
    (comb : FiniteCombination t) (ζ : ℝ) : Kernel :=
  combinationKernel A B β t comb++kernelScale ζ (priceQuadraticKernel L t)

def separatedValueCoefficient {H : ℕ} (L : WindowPrice H) (t : ℝ)
    (comb : FiniteCombination t) (ζ : ℝ) (n : ℕ) : ℝ :=
  combinationValueCoefficient comb n+ζ*priceValueLagCoefficient L t n

theorem separated_value_charge {H : ℕ} (L : WindowPrice H) (t : ℝ)
    (comb : FiniteCombination t) (hmem : ∀ n∈comb.lags,n≤H) (ζ : ℝ)
    (hcharge : comb.charge+ζ*stationaryPriceCharge L t=0) :
    (∑ n∈Finset.Icc 0 H,separatedValueCoefficient L t comb ζ n)=0 := by
  unfold separatedValueCoefficient
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have hc:=sum_combinationValueCoefficient_Icc comb hmem (fun _ => 1)
  simp only [mul_one] at hc
  rw [hc,sum_combinationValueCoefficient]
  have hp:=sum_priceValueLagCoefficient_Icc_zero L t (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp]
  change 4*comb.charge+ζ*priceValueCharge L t=0
  rw [priceValueCharge_eq]
  nlinarith

theorem separated_kernel_symbol_le {H : ℕ} {A B β t ε ζ : ℝ}
    (hB : B≠0) (L : WindowPrice H) (comb : FiniteCombination t)
    (hcharge : comb.charge+ζ*stationaryPriceCharge L t=0)
    (hsymbol : ∀ c,symbol (Waves.multiplierMap A B β t) t comb.lags comb.α comb.β
      comb.γplus comb.γminus c+ζ*stationaryPriceIntegrand L (Waves.multiplierMap A B β t) t c≤ -ε) :
    ∀ θ,kernelSymbol (separatedKernel L A B β t comb ζ) θ≤ -ε := by
  apply kernelSymbol_le_of_halfCircle
  intro ω hω0 hωπ
  let c : Frequency:=⟨Real.cos ω,Real.neg_one_le_cos ω,Real.cos_le_one ω⟩
  have hc : Real.arccos c=ω:=Real.arccos_cos hω0 hωπ
  rw [←hc]
  simp only [separatedKernel,kernelSymbol_append,kernelSymbol_scale,
    kernelSymbol_combination A B β t hB comb c,kernelSymbol_priceQuadratic]
  have hs:=hsymbol c
  rw [stationaryPriceIntegrand_eq,priceValueCharge_eq] at hs
  have hch:=congrArg (fun z : ℝ => 2*z*(Waves.multiplierMap A B β t c).re) hcharge
  simp only [mul_zero,zero_mul] at hch
  nlinarith

theorem separated_kernel_source_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β t ζ : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (comb : FiniteCombination t)
    (hmem : ∀ n∈comb.lags,n≤H) (r : HRun E A B β H) (hr : ZeroPriceRun L r)
    (k : ℕ) (hk : 1≤k) :
    0≤kernelEval (separatedKernel L A B β t comb ζ) (discountedInteger r.x t) k+
      finiteValueCombination (Finset.Icc 0 H) (separatedValueCoefficient L t comb ζ)
        (discountedValue (sampleValue r) t) k := by
  let h:=discountedValue (sampleValue r) t
  have hv : finiteValueCombination (Finset.Icc 0 H) (separatedValueCoefficient L t comb ζ) h k=
      combinationValue comb h k+ζ*(∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n*h (k+n)) := by
    unfold finiteValueCombination separatedValueCoefficient
    simp_rw [add_mul,mul_assoc]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,
      sum_combinationValueCoefficient_Icc comb hmem,←combinationValue_eq_coefficients]
    have he:=sum_priceValueLagCoefficient_Icc_zero L t (fun n => h (k+n))
    rw [he,sum_priceValueLagCoefficient]
    simp only [Nat.add_assoc]
  have hprice:=hRun_priceBandedEval r L t k
  change _+ (∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n*h (k+n))=
    Real.exp (-2*(k : ℝ)*t)*L (runWindow r (k+H)) at hprice
  rw [hr (k+H) (by omega),mul_zero] at hprice
  have hp:=congrArg (fun z : ℝ => ζ*z) hprice
  simp only [mul_zero] at hp
  have hslack:=hRun_combinationSlack_nonneg r comb hmem k hk
  rw [combinationSlack_eq] at hslack
  change 0≤combinationQuadratic comb (discountedPosition r.x t) (discountedPosition r.σ t) k+
    combinationValue comb h k at hslack
  rw [separatedKernel,kernelEval_append,kernelEval_scale,hv,hRun_kernelEval_combination r comb hB k hk]
  nlinarith

theorem exists_prefactor_of_stationary_price {A B β T : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    (hstationary : ∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (Waves.multiplierMap A B β T) T H ν C →
      0<L (stationaryWindow ν (Waves.multiplierMap A B β T) C T H)) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope A B β H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨w,ζ,ε,hw,hε,hcharge,hsymbol⟩:=stationary_kernel_separation L
    (Waves.multiplierMap A B β T) T hstationary
  let comb:=separationCombination T H w hw
  have hmem : ∀ n∈comb.lags,n≤H:=fun n hn => (Finset.mem_Icc.mp hn).2
  have hch : comb.charge+ζ*stationaryPriceCharge L T=0:=hcharge
  have hs : ∀ c,symbol (Waves.multiplierMap A B β T) T comb.lags comb.α comb.β
      comb.γplus comb.γminus c+ζ*stationaryPriceIntegrand L (Waves.multiplierMap A B β T) T c≤ -ε:=hsymbol
  exact exists_prefactor_of_kernel_banded hB L hRate hpos hstep
    (separatedKernel L A B β T comb ζ) (Finset.Icc 0 H) (separatedValueCoefficient L T comb ζ)
    hε (separated_kernel_symbol_le hB L comb hch hs) (separated_value_charge L T comb hmem ζ hch)
    1 (fun d r hr k hk => separated_kernel_source_nonneg hB L comb hmem r hr k hk)

end polyak.FiniteHorizon
