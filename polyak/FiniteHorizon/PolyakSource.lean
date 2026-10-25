import polyak.FiniteHorizon.KernelMatrix
import polyak.FiniteHorizon.ExactPrices
import polyak.Energy.CombinationSupport
import polyak.Boundary.Certificate

/-!
Article: Appendix C, the actual normalized interpolation source at common width.
Use: normalized lower-one and upper branch weights have zero value charge.
Their true recurrence-eliminated kernel, shifted by one coordinate, supplies
the source matrix and sampled-value coefficients used by the price construction.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Waves Duality
open scoped BigOperators

def normalizedCombination (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ) : FiniteCombination t where
  lags:=insert 1 W.lags
  positive_lag n hn:=by
    rcases Finset.mem_insert.mp hn with rfl|hn
    · exact le_rfl
    · exact W.positive_lag n hn
  α:=lowerWeight
  β:=upperWeight W (Real.cosh t)
  α_nonneg n _:=by unfold lowerWeight; split_ifs <;> norm_num
  β_nonneg n _:=by
    unfold upperWeight
    split_ifs with hn
    · exact div_nonneg (W.nonneg n hn) (lagDenominator_pos (Real.one_le_cosh t) n (W.positive_lag n hn)).le
    · exact le_rfl
  γplus:=γ
  γminus:=γ
  γplus_nonneg:=hγ
  γminus_nonneg:=hγ

theorem normalizedCombination_charge (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ) :
    (normalizedCombination W t γ hγ).charge=0 := by
  unfold FiniteCombination.charge normalizedCombination
  rw [normalizedWeights_cancel]
  ring

theorem normalizedCombination_lag_le_five (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ)
    (hW : ∀ n∈W.lags,n≤5) : ∀ n∈(normalizedCombination W t γ hγ).lags,n≤5 := by
  intro n hn
  rcases Finset.mem_insert.mp hn with rfl|hn
  · norm_num
  · exact hW n hn

def normalizedKernel7 (W : DualWeights) (q t γ : ℝ) (hγ : 0≤γ) : Kernel :=
  combinationKernel 0 (2*q) (q^2) t (normalizedCombination W t γ hγ)

def normalizedMatrix7 (W : DualWeights) (q t γ : ℝ) (hγ : 0≤γ) : WindowMatrix7 :=
  kernelMatrix7 (normalizedKernel7 W q t γ hγ)

def normalizedValues7 (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ) (a : ℕ) : ℝ :=
  if a=0 then 0 else combinationValueCoefficient (normalizedCombination W t γ hγ) (a-1)

theorem normalizedKernel7_supported (W : DualWeights) (q t γ : ℝ) (hγ : 0≤γ)
    (hW : ∀ n∈W.lags,n≤5) : KernelSupported (-1) 6 (normalizedKernel7 W q t γ hγ) := by
  exact combinationKernel_supported 0 (2*q) (q^2) (normalizedCombination W t γ hγ) 5
    (normalizedCombination_lag_le_five W t γ hγ hW)

theorem normalizedValues7_zero (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ) :
    normalizedValues7 W t γ hγ 0=0:=by simp [normalizedValues7]

theorem normalizedValues7_succ (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ) (n : ℕ) :
    normalizedValues7 W t γ hγ (n+1)=combinationValueCoefficient (normalizedCombination W t γ hγ) n:=by
  simp [normalizedValues7]

theorem range_seven_eq : Finset.range 7=Finset.Icc 0 6 := by
  ext n
  simp only [Finset.mem_range,Finset.mem_Icc]
  omega

theorem normalizedValues7_charge (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ)
    (hW : ∀ n∈W.lags,n≤5) : ∑ a∈Finset.range 8,normalizedValues7 W t γ hγ a=0 := by
  rw [Finset.sum_range_succ']
  simp_rw [normalizedValues7_succ]
  rw [normalizedValues7_zero,add_zero,range_seven_eq]
  have hmem : ∀ n∈(normalizedCombination W t γ hγ).lags,n≤6:=by
    intro n hn
    exact (normalizedCombination_lag_le_five W t γ hγ hW n hn).trans (by norm_num)
  have he:=sum_combinationValueCoefficient_Icc (normalizedCombination W t γ hγ) hmem (fun _ => 1)
  simp only [mul_one] at he
  rw [he,sum_combinationValueCoefficient,normalizedCombination_charge,mul_zero]

local instance : Fact (0<2*Real.pi):=⟨Real.two_pi_pos⟩

theorem frequencyCosine_coe (ω : ℝ) : frequencyCosine (ω : FrequencyCircle)=Real.cos ω := by
  unfold frequencyCosine
  rw [character_re_coe]
  norm_num

theorem kernelSymbol_eq_frequencyCosine (K : Kernel) (F : ℝ → ℝ)
    (h : ∀ ω : ℝ,0≤ω → ω≤Real.pi → kernelSymbol K (ω : FrequencyCircle)=F (Real.cos ω)) :
    ∀ θ,kernelSymbol K θ=F (frequencyCosine θ) := by
  intro θ
  let a:=AddCircle.equivIco (2*Real.pi) (-Real.pi) θ
  have ha : -Real.pi≤(a : ℝ) ∧ (a : ℝ)< -Real.pi+2*Real.pi:=a.property
  have he : ((a : ℝ) : FrequencyCircle)=θ:=AddCircle.coe_equivIco
  rw [←he,frequencyCosine_coe]
  by_cases hpos : 0≤(a : ℝ)
  · exact h a hpos (by linarith [ha.2])
  · have hn:=h (-(a : ℝ)) (by linarith) (by linarith [ha.1])
    change kernelSymbol K (-((a : ℝ) : FrequencyCircle))=F (Real.cos (-(a : ℝ))) at hn
    rwa [kernelSymbol_neg,Real.cos_neg] at hn

theorem normalizedMatrix7_symbol (W : DualWeights) {q : ℝ} (hq : 0<q)
    (t γ : ℝ) (hγ : 0≤γ) (hW : ∀ n∈W.lags,n≤5) (θ : FrequencyCircle) :
    coefficientSymbol (normalizedMatrix7 W q t γ hγ) θ=
      dualSymbol W (Real.sinh (t-Real.log q)) (Real.cosh t) (frequencyCosine θ)+
        2*γ*Spectral.g (Real.sinh (t-Real.log q)) (frequencyCosine θ) := by
  rw [normalizedMatrix7,kernelMatrix7_symbol _ (normalizedKernel7_supported W q t γ hγ hW)]
  refine kernelSymbol_eq_frequencyCosine _ (fun c =>
    dualSymbol W (Real.sinh (t-Real.log q)) (Real.cosh t) c+
      2*γ*Spectral.g (Real.sinh (t-Real.log q)) c) ?_ θ
  intro ω hω0 hωπ
  let c : Frequency:=⟨Real.cos ω,Real.neg_one_le_cos ω,Real.cos_le_one ω⟩
  have hc : Real.arccos c=ω:=Real.arccos_cos hω0 hωπ
  rw [←hc]
  unfold normalizedKernel7
  rw [kernelSymbol_combination 0 (2*q) (q^2) t (by positivity),normalizedCombination_charge,
    mul_zero,zero_mul,sub_zero,Waves.multiplierMap_polyak q t hq]
  simpa only [normalizedCombination,Real.cos_arccos c.property.1 c.property.2] using
    normalizedWeights_symbol W (t-Real.log q) t γ c

theorem normalizedValues7_eval (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ)
    (h : ℤ → ℝ) (j : ℤ) :
    (∑ a∈Finset.range 8,normalizedValues7 W t γ hγ a*h (j-1+(a : ℤ)))=
      ∑ n∈Finset.Icc 0 6,combinationValueCoefficient (normalizedCombination W t γ hγ) n*
        h (j+(n : ℤ)) := by
  rw [Finset.sum_range_succ']
  simp_rw [normalizedValues7_succ]
  simp only [normalizedValues7_zero,zero_mul,add_zero]
  rw [range_seven_eq]
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  push_cast
  ring

theorem normalizedBanded7_eval (W : DualWeights) (q t γ : ℝ) (hγ : 0≤γ)
    (hW : ∀ n∈W.lags,n≤5) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    bandedFunctional7 (normalizedMatrix7 W q t γ hγ) (normalizedValues7 W t γ hγ) f h (j-1)=
      kernelEval (normalizedKernel7 W q t γ hγ) f j+
        ∑ n∈Finset.Icc 0 6,combinationValueCoefficient (normalizedCombination W t γ hγ) n*h (j+(n : ℤ)) := by
  rw [bandedFunctional7,normalizedMatrix7,
    kernelMatrix7_eval _ (normalizedKernel7_supported W q t γ hγ hW),normalizedValues7_eval]

theorem normalizedBanded7_source (W : DualWeights) {q : ℝ} (hq : 0<q)
    (t γ : ℝ) (hγ : 0≤γ) (hW : ∀ n∈W.lags,n≤5) (H : ℕ) (hH : 7≤H) :
    BandedSource7 0 (2*q) (q^2) t H (normalizedMatrix7 W q t γ hγ) (normalizedValues7 W t γ hγ) := by
  intro E _ _ r k hk
  let l:=k-5
  have hl : 1≤l:=by dsimp [l]; omega
  have hj : (k : ℤ)-6=(l : ℤ)-1:=by dsimp [l]; omega
  rw [hj,normalizedBanded7_eval W q t γ hγ hW]
  let comb:=normalizedCombination W t γ hγ
  have hmem6 : ∀ n∈comb.lags,n≤6:=by
    intro n hn
    exact (normalizedCombination_lag_le_five W t γ hγ hW n hn).trans (by omega)
  have hmemH : ∀ n∈comb.lags,n≤H:=by
    intro n hn
    exact (hmem6 n hn).trans (by omega)
  have hker : kernelEval (normalizedKernel7 W q t γ hγ)
      (integerDiscount (fun z => r.x z.toNat) t) l=
        kernelEval (normalizedKernel7 W q t γ hγ) (discountedInteger r.x t) l := by
    unfold kernelEval
    congr 1
    apply List.map_congr_left
    intro p hp
    have hb:=normalizedKernel7_supported W q t γ hγ hW p hp
    rw [←integerDiscount_nat_nonneg r.x t _ (by omega),
      ←integerDiscount_nat_nonneg r.x t _ (by omega)]
  have hval : (∑ n∈Finset.Icc 0 6,combinationValueCoefficient comb n*
      integerDiscountValue (fun z => sampleValue r z.toNat) t ((l : ℤ)+(n : ℤ)))=
      combinationValue comb (discountedValue (sampleValue r) t) l := by
    rw [combinationValue_eq_coefficients,
      ←sum_combinationValueCoefficient_Icc comb hmem6 (fun n => discountedValue (sampleValue r) t (l+n))]
    apply Finset.sum_congr rfl
    intro n _
    rw [←integerDiscountValue_nat_nonneg (sampleValue r) t _ (by omega)]
    have hn : ((l : ℤ)+(n : ℤ)).toNat=l+n:=by omega
    rw [hn]
  rw [hker,hval]
  change 0≤kernelEval (combinationKernel 0 (2*q) (q^2) t comb) (discountedInteger r.x t) l+
    combinationValue comb (discountedValue (sampleValue r) t) l
  rw [hRun_kernelEval_combination r comb (by positivity) l hl]
  rw [←combinationSlack_eq]
  exact hRun_combinationSlack_nonneg r comb hmemH l hl

end polyak.FiniteHorizon
