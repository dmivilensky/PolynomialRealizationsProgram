import polyak.FiniteHorizon.PolyakSource
import polyak.Energy.KernelSize

/-!
Article: Appendix C, uniform size of the actual normalized source coefficients.
Use: the upper weights are at most one, only five lags occur, and every filter
coefficient is bounded on a bounded exponent interval. No continuity or unique
choice of branch weights is required.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary
open scoped BigOperators

theorem lagDenominator_one_le {G : ℝ} (hG : 1≤G) {n : ℕ} (hn : 1≤n) :
    1≤lagDenominator G n := by
  have hh:=degree_le_chebU (n-1) hG
  have he : ((n-1 : ℕ) : ℝ)+1=n:=by exact_mod_cast Nat.sub_add_cancel hn
  rw [he] at hh
  exact (Nat.one_le_cast.mpr hn).trans hh

theorem dualWeight_le_one (W : DualWeights) {n : ℕ} (hn : n∈W.lags) : W.weight n≤1 := by
  rw [←W.sum_one]
  exact Finset.single_le_sum (fun j hj => W.nonneg j hj) hn

theorem upperWeight_le_one (W : DualWeights) {G : ℝ} (hG : 1≤G) (n : ℕ) : upperWeight W G n≤1 := by
  unfold upperWeight
  split_ifs with hn
  · apply (div_le_one (lagDenominator_pos hG n (W.positive_lag n hn))).mpr
    exact (dualWeight_le_one W hn).trans (lagDenominator_one_le hG (W.positive_lag n hn))
  · norm_num

theorem lowerWeight_le_one (n : ℕ) : lowerWeight n≤1 := by unfold lowerWeight; split_ifs <;> norm_num

theorem normalizedCombination_card_le_five (W : DualWeights) (t γ : ℝ) (hγ : 0≤γ)
    (hW : ∀ n∈W.lags,n≤5) : (normalizedCombination W t γ hγ).lags.card≤5 := by
  have hsub : (normalizedCombination W t γ hγ).lags⊆Finset.Icc 1 5:=by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(normalizedCombination W t γ hγ).positive_lag n hn,
      normalizedCombination_lag_le_five W t γ hγ hW n hn⟩
  have hh:=Finset.card_le_card hsub
  norm_num at hh
  exact hh

def normalizedGradientBound (q R : ℝ) : ℝ:=(1+q^2)*Real.exp R/(2*q)

def normalizedLagBound (q R : ℝ) : ℝ:=
  (1/4 : ℝ)*(1+Real.exp (5*R))^2*(1+normalizedGradientBound q R)^2

def normalizedSourceBound (q R : ℝ) : ℝ:=
  20*Real.exp (5*R)*normalizedLagBound q R+2*(1+normalizedGradientBound q R)^2+40*Real.exp (5*R)

theorem normalizedGradientBound_nonneg {q : ℝ} (hq : 0<q) (R : ℝ) :
    0≤normalizedGradientBound q R:=by unfold normalizedGradientBound; positivity

theorem gradientFilter_size_le {q R t : ℝ} (hq : 0<q) (ht : |t|≤R) :
    filterSize (gradientFilter 0 (2*q) (q^2) t)≤normalizedGradientBound q R := by
  have he : Real.exp t≤Real.exp R:=Real.exp_le_exp.mpr ((le_abs_self t).trans ht)
  have hn : Real.exp (-t)≤Real.exp R:=Real.exp_le_exp.mpr ((neg_le_abs t).trans ht)
  have hid : filterSize (gradientFilter 0 (2*q) (q^2) t)=
      (Real.exp t+q^2*Real.exp (-t))/(2*q) := by
    simp only [gradientFilter,filterSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      zero_div,neg_zero,abs_zero,add_zero,abs_div,abs_mul,abs_of_pos hq,abs_sq,
      abs_of_pos (Real.exp_pos _)]
    norm_num
    ring
  rw [hid]
  unfold normalizedGradientBound
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ)≤2*q)
  nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg q)]

theorem exp_lag_le {t R : ℝ} (ht : |t|≤R) {n : ℕ} (hn : n≤5) :
    Real.exp (n*t)≤Real.exp (5*R) ∧ Real.exp (-(n*t))≤Real.exp (5*R) := by
  have hR : 0≤R:=(abs_nonneg t).trans ht
  have h0 : (0 : ℝ)≤n:=Nat.cast_nonneg _
  have h5 : (n : ℝ)≤5:=by exact_mod_cast hn
  have hmul:=mul_le_mul_of_nonneg_left ht h0
  have hbound:=mul_le_mul_of_nonneg_right h5 hR
  have ha : |(n : ℝ)*t|≤5*R:=by
    rw [abs_mul,abs_of_nonneg h0]
    exact hmul.trans hbound
  exact ⟨Real.exp_le_exp.mpr ((le_abs_self _).trans ha),
    Real.exp_le_exp.mpr ((neg_le_abs _).trans ha)⟩

theorem lagKernel_size_le {q t R : ℝ} (hq : 0<q) (ht : |t|≤R) {n : ℕ} (hn : n≤5)
    (δ : ℝ) (hδ : |δ|=1) :
    kernelSize (lagKernel 0 (2*q) (q^2) t n δ)≤normalizedLagBound q R := by
  rw [lagKernel_size _ _ _ _ _ _ hδ]
  have he:=(exp_lag_le ht hn).1
  have hg:=gradientFilter_size_le hq ht
  have hgp:=filterSize_nonneg (gradientFilter 0 (2*q) (q^2) t)
  unfold normalizedLagBound
  gcongr

theorem combinationKernel_size {A B β t : ℝ} (comb : FiniteCombination t) :
    kernelSize (combinationKernel A B β t comb)=
      (∑ n∈comb.lags,2*Real.exp (-(n*t))*(comb.α n+comb.β n)*
        ((1/4 : ℝ)*(1+Real.exp (n*t))^2*(1+filterSize (gradientFilter A B β t))^2))+
      (comb.γplus+comb.γminus)*(1+filterSize (gradientFilter A B β t))^2 := by
  have hsum : kernelSize (comb.lags.toList.flatMap fun (n : ℕ) =>
      kernelScale (2*Real.exp (-(n*t)))
        (kernelScale (comb.α n) (lagKernel A B β t n 1)++
          kernelScale (comb.β n) (lagKernel A B β t n (-1))))=
      ∑ n∈comb.lags,2*Real.exp (-(n*t))*(comb.α n+comb.β n)*
        ((1/4 : ℝ)*(1+Real.exp (n*t))^2*(1+filterSize (gradientFilter A B β t))^2) := by
    rw [kernelSize_flatMap,Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro n hn
    rw [kernelSize_scale,kernelSize_append,kernelSize_scale,kernelSize_scale,
      lagKernel_size _ _ _ _ _ 1 (by norm_num),lagKernel_size _ _ _ _ _ (-1) (by norm_num)]
    rw [abs_of_pos (by positivity : 0<2*Real.exp (-(n*t))),
      abs_of_nonneg (comb.α_nonneg n hn),abs_of_nonneg (comb.β_nonneg n hn)]
    ring
  have hplus : kernelSize (kernelScale (4*comb.γplus) (starKernel 1 unitFilter (gradientFilter A B β t)))=
      comb.γplus*(1+filterSize (gradientFilter A B β t))^2 := by
    rw [kernelSize_scale,starKernel_size 1 (by norm_num),filterSize_unit,
      abs_of_nonneg (mul_nonneg (by norm_num) comb.γplus_nonneg)]
    ring
  have hminus : kernelSize (kernelScale (4*comb.γminus) (starKernel (-1) unitFilter (gradientFilter A B β t)))=
      comb.γminus*(1+filterSize (gradientFilter A B β t))^2 := by
    rw [kernelSize_scale,starKernel_size (-1) (by norm_num),filterSize_unit,
      abs_of_nonneg (mul_nonneg (by norm_num) comb.γminus_nonneg)]
    ring
  rw [combinationKernel,kernelSize_append,kernelSize_append,hsum,hplus,hminus]
  ring

theorem normalizedKernel7_size_le (W : DualWeights) {q t γ R : ℝ} (hq : 0<q)
    (ht : |t|≤R) (hγ : 0≤γ) (hγ1 : γ≤1) (hW : ∀ n∈W.lags,n≤5) :
    kernelSize (normalizedKernel7 W q t γ hγ)≤
      20*Real.exp (5*R)*normalizedLagBound q R+2*(1+normalizedGradientBound q R)^2 := by
  let comb:=normalizedCombination W t γ hγ
  let E:=Real.exp (5*R)
  let L:=normalizedLagBound q R
  have hL : 0≤L:=by dsimp [L,normalizedLagBound]; positivity
  have hsum : (∑ n∈comb.lags,2*Real.exp (-(n*t))*(comb.α n+comb.β n)*
      ((1/4 : ℝ)*(1+Real.exp (n*t))^2*(1+filterSize (gradientFilter 0 (2*q) (q^2) t))^2))≤
      20*E*L := by
    have hterm (n : ℕ) (hn : n∈comb.lags) :
        2*Real.exp (-(n*t))*(comb.α n+comb.β n)*
          ((1/4 : ℝ)*(1+Real.exp (n*t))^2*(1+filterSize (gradientFilter 0 (2*q) (q^2) t))^2)≤4*E*L := by
      have hn5:=normalizedCombination_lag_le_five W t γ hγ hW n hn
      have he:=(exp_lag_le ht hn5).2
      have hw : comb.α n+comb.β n≤2:=by
        have ha:=lowerWeight_le_one n
        have hb:=upperWeight_le_one W (Real.one_le_cosh t) n
        change lowerWeight n+upperWeight W (Real.cosh t) n≤2
        linarith
      have hl:=lagKernel_size_le hq ht hn5 1 (by norm_num)
      rw [lagKernel_size _ _ _ _ _ 1 (by norm_num)] at hl
      have hs : 2*Real.exp (-(n*t))*(comb.α n+comb.β n)≤4*E := by
        have hnn : 0≤comb.α n+comb.β n:=add_nonneg (comb.α_nonneg n hn) (comb.β_nonneg n hn)
        nlinarith [mul_le_mul he hw hnn (Real.exp_pos (5*R)).le]
      exact mul_le_mul hs hl (by positivity) (by dsimp [E]; positivity)
    calc
      _≤∑ _n∈comb.lags,4*E*L:=Finset.sum_le_sum hterm
      _=(comb.lags.card : ℝ)*(4*E*L):=by simp
      _≤5*(4*E*L):=mul_le_mul_of_nonneg_right
        (by exact_mod_cast normalizedCombination_card_le_five W t γ hγ hW) (by positivity)
      _=_:=by ring
  have hstar : (comb.γplus+comb.γminus)*(1+filterSize (gradientFilter 0 (2*q) (q^2) t))^2≤
      2*(1+normalizedGradientBound q R)^2 := by
    change (γ+γ)*_≤_
    have hg:=gradientFilter_size_le hq ht
    have hgn:=filterSize_nonneg (gradientFilter 0 (2*q) (q^2) t)
    gcongr
    linarith
  rw [normalizedKernel7,combinationKernel_size]
  exact add_le_add hsum hstar

theorem normalized_shift_coefficient_abs_le (W : DualWeights) {t γ R : ℝ}
    (ht : |t|≤R) (hγ : 0≤γ) (hW : ∀ n∈W.lags,n≤5)
    {n : ℕ} (hn : n∈(normalizedCombination W t γ hγ).lags) :
    |combinationShiftCoefficient (normalizedCombination W t γ hγ) n|≤4*Real.exp (5*R) := by
  let comb:=normalizedCombination W t γ hγ
  have hn5:=normalizedCombination_lag_le_five W t γ hγ hW n hn
  have he:=(exp_lag_le ht hn5).1
  have hsum : comb.α n+comb.β n≤2:=by
    have ha:=lowerWeight_le_one n
    have hb:=upperWeight_le_one W (Real.one_le_cosh t) n
    change lowerWeight n+upperWeight W (Real.cosh t) n≤2
    linarith
  have hdiff : |comb.α n-comb.β n|≤2 := by
    calc
      _≤|comb.α n|+|comb.β n|:=abs_sub _ _
      _=comb.α n+comb.β n:=by rw [abs_of_nonneg (comb.α_nonneg n hn),abs_of_nonneg (comb.β_nonneg n hn)]
      _≤_:=hsum
  change |2*Real.exp (n*t)*(comb.α n-comb.β n)|≤_
  rw [abs_mul,abs_of_pos (by positivity : 0<2*Real.exp (n*t))]
  have hh:=mul_le_mul he hdiff (abs_nonneg _) (Real.exp_pos (5*R)).le
  nlinarith

theorem normalizedValues7_mass_le (W : DualWeights) {t γ R : ℝ}
    (ht : |t|≤R) (hγ : 0≤γ) (hW : ∀ n∈W.lags,n≤5) :
    (∑ a∈Finset.range 8,|normalizedValues7 W t γ hγ a|)≤40*Real.exp (5*R) := by
  rw [Finset.sum_range_succ']
  simp_rw [normalizedValues7_succ]
  simp only [normalizedValues7_zero,abs_zero,add_zero]
  rw [range_seven_eq]
  let comb:=normalizedCombination W t γ hγ
  have hsub : insert 0 comb.lags⊆Finset.Icc 0 6:=by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl|hn
    · norm_num
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
        (normalizedCombination_lag_le_five W t γ hγ hW n hn).trans (by norm_num)⟩
  have he : (∑ n∈Finset.Icc 0 6,|combinationValueCoefficient comb n|)=
      ∑ n∈insert 0 comb.lags,|combinationValueCoefficient comb n| := by
    symm
    apply Finset.sum_subset hsub
    intro n _ hn
    have h0 : n≠0:=by intro hh; subst n; exact hn (Finset.mem_insert_self _ _)
    have hlag : n∉comb.lags:=by intro hh; exact hn (Finset.mem_insert_of_mem hh)
    simp only [combinationValueCoefficient,ite_eq_right h0,ite_eq_right hlag,abs_zero]
  rw [he,Finset.sum_insert (combination_zero_not_mem comb)]
  have hlag : (∑ n∈comb.lags,|combinationValueCoefficient comb n|)=
      ∑ n∈comb.lags,|combinationShiftCoefficient comb n| := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n≠0:=by have := comb.positive_lag n hn; omega
    simp only [combinationValueCoefficient,ite_eq_right hn0,ite_eq_left hn]
  rw [hlag]
  have h0 : combinationValueCoefficient comb 0= -∑ n∈comb.lags,combinationShiftCoefficient comb n := by
    simp only [combinationValueCoefficient,ite_true]
    have hc : comb.charge=0:=normalizedCombination_charge W t γ hγ
    rw [hc,mul_zero,zero_sub]
  rw [h0,abs_neg]
  have hs : (∑ n∈comb.lags,|combinationShiftCoefficient comb n|)≤20*Real.exp (5*R) := by
    calc
      _≤∑ _n∈comb.lags,4*Real.exp (5*R):=Finset.sum_le_sum fun n hn =>
        normalized_shift_coefficient_abs_le W ht hγ hW hn
      _=(comb.lags.card : ℝ)*(4*Real.exp (5*R)):=by simp
      _≤5*(4*Real.exp (5*R)):=mul_le_mul_of_nonneg_right
        (by exact_mod_cast normalizedCombination_card_le_five W t γ hγ hW) (by positivity)
      _=_:=by ring
  have ha:=Finset.abs_sum_le_sum_abs (fun n => combinationShiftCoefficient comb n) comb.lags
  nlinarith

theorem normalized_source_size_le (W : DualWeights) {q t γ R : ℝ} (hq : 0<q)
    (ht : |t|≤R) (hγ : 0≤γ) (hγ1 : γ≤1) (hW : ∀ n∈W.lags,n≤5) :
    bandedSize7 (normalizedMatrix7 W q t γ hγ) (normalizedValues7 W t γ hγ)≤normalizedSourceBound q R := by
  have hK:=normalizedKernel7_size_le W hq ht hγ hγ1 hW
  have hV:=normalizedValues7_mass_le W ht hγ hW
  have hC:=kernelMatrix7_mass_le (normalizedKernel7 W q t γ hγ)
  unfold bandedSize7 normalizedMatrix7 normalizedSourceBound
  linarith

end polyak.FiniteHorizon
