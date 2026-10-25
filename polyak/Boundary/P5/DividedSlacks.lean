import polyak.Boundary.P5.System
import polyak.Boundary.P5.CriticalSlacks
import polyak.Boundary.P5.CycleValues
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: Proposition p5divslack, the actual first-order divided slacks.
Use: every lag along every continuous branch through the critical point,
without assuming a derivative of that branch. The finite lags below the uniform
P5 tail can therefore be settled simultaneously.
-/

noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology

/-- Article: the derivative of h times a continuous blown-up coordinate. -/
theorem parameter_mul_hasDerivAt {f : ℝ → ℝ} (hf : ContinuousAt f 0) :
    HasDerivAt (fun h => h*f h) (f 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have ht : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h≠0 := by simpa using hh
  simp [smul_eq_mul,hh']

/-- Article: the actual raw two-atom slack along a blown-up parameter tuple. -/
def rawBranch (h : ℝ) (Z : Coordinates) (n : ℕ) (σ : ℝ) : ℝ :=
  (1-h*Z 3)*actualRaw (1/2+h*Z 0) (1+h) n σ (-1/2+h*Z 1)+
    h*Z 3*actualRaw (1/2+h*Z 0) (1+h) n σ (Z 2)-
      σ*h*Z 4*lagDenominator (1+h) n

/-- Article: the exact main-atom contribution before residue-class simplification. -/
def mainFirstDerivative (A B : ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  (B-A)*(1-chebT n (-1/2))+
    (1/2)*((n : ℝ)^2-(Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval (-1/2)*B)+
    σ*((3/2*A+B)*chebU (n-1) (-1/2)+
      (3/4)*(Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)).derivative.eval (-1/2)*B)

/-- Article: the main atom's genuine derivative along any continuous blown-up branch. -/
theorem main_actualRaw_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) (n : ℕ) (σ : ℝ) :
    HasDerivAt (fun h => actualRaw (1/2+h*Z h 0) (1+h) n σ (-1/2+h*Z h 1))
      (mainFirstDerivative A₀ B₀ n σ) 0 := by
  have hz (i : Fin 7) : ContinuousAt (fun h => Z h i) 0 :=
    (continuous_apply i).continuousAt.comp hZ
  have hu : HasDerivAt (fun h => 1/2+h*Z h 0) A₀ 0 := by
    simpa [hZ0] using (parameter_mul_hasDerivAt (hz 0)).const_add (1/2)
  have hx : HasDerivAt (fun h => -1/2+h*Z h 1) B₀ 0 := by
    simpa [hZ0] using (parameter_mul_hasDerivAt (hz 1)).const_add (-1/2)
  have hg : HasDerivAt (fun h : ℝ => 1+h) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
  have htG := ((Polynomial.Chebyshev.T ℝ (n : ℤ)).hasDerivAt (1+(0 : ℝ))).comp 0 hg
  have htx := ((Polynomial.Chebyshev.T ℝ (n : ℤ)).hasDerivAt (-1/2+(0 : ℝ)*Z 0 1)).comp 0 hx
  have hux := ((Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)).hasDerivAt (-1/2+(0 : ℝ)*Z 0 1)).comp 0 hx
  have hgap := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hx.pow 2)).sub (hu.pow 2)
  have hsin := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hx.pow 2)
  have hd := (hgap.mul (htG.sub htx)).add ((((hu.const_mul 2).mul hsin).mul hux).const_mul σ)
  convert hd using 1
  · rfl
  · dsimp only [mainFirstDerivative,chebT,chebU,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
    norm_num only [zero_mul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,
      Polynomial.Chebyshev.derivative_T_eval_one,Polynomial.Chebyshev.T_eval_one,Int.cast_natCast]
    ring

/-- Article: residue-free simplification of the genuine main-atom derivative. -/
theorem mainFirstDerivative_eq (A B : ℝ) (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    mainFirstDerivative A B n σ=(B-A)*(1-chebT n (-1/2))+(n : ℝ)^2/2-
      n*B*chebU (n-1) (-1/2)/2+
      σ*((3/2*A+B/2)*chebU (n-1) (-1/2)-n*B*chebT n (-1/2)) := by
  rw [mainFirstDerivative,chebT_derivative_eval n hn]
  have hu := chebU_derivative_cycle n hn
  linear_combination σ*B*hu

/-- Article: the critical three-cycle slack vanishes at every critical pair. -/
theorem critical_actualRaw_zero {n : ℕ} (hn : 1≤n) {σ : ℝ} (hc : CriticalPair n σ) :
    actualRaw (1/2) 1 n σ (-1/2)=0 := by
  have hT : chebT n (1 : ℝ)=1 := by simp [chebT]
  unfold actualRaw g lagB
  rw [hT,chebT_cycle,chebU_lag_cycle n hn]
  rcases hc with ⟨hs,hc⟩
  rcases hc with hc | ⟨hc,rfl⟩ | ⟨hc,rfl⟩ <;> norm_num [hc]

/-- Article: the genuine derivative equals the source first-order slack at every critical lag. -/
theorem critical_firstDerivative_eq {n : ℕ} (hn : 1≤n) {σ : ℝ} (hc : CriticalPair n σ) :
    mainFirstDerivative A₀ B₀ n σ+P₀*criticalY n σ y₀-σ*D₀*n=firstSlack n σ := by
  rw [mainFirstDerivative_eq A₀ B₀ n hn]
  rw [chebT_cycle,chebU_lag_cycle n hn]
  unfold firstSlack
  rcases hc with ⟨hs,hc⟩
  rcases hc with hc | ⟨hc,rfl⟩ | ⟨hc,rfl⟩ <;> norm_num [hc] <;> ring

/-- Article: the positive Chebyshev normalization at the critical point. -/
theorem lagDenominator_one (n : ℕ) (hn : 1≤n) : lagDenominator 1 n=(n : ℝ) := by
  simp only [lagDenominator,chebU,Polynomial.Chebyshev.U_eval_one,Int.cast_natCast]
  exact_mod_cast Nat.sub_add_cancel hn

/-- Article: the auxiliary atom contributes exactly Y at the critical point. -/
theorem auxiliary_actualRaw_eq (n : ℕ) (σ y : ℝ) :
    actualRaw (1/2) 1 n σ y=criticalY n σ y := by
  have ht : chebT n (1 : ℝ)=1 := by simp [chebT]
  unfold actualRaw criticalY g lagB
  rw [ht]
  ring

/-- Article: the actual raw slack derivative is the source first-order coefficient. -/
theorem rawBranch_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) {n : ℕ} (hn : 1≤n) {σ : ℝ} (hc : CriticalPair n σ) :
    HasDerivAt (fun h => rawBranch h (Z h) n σ) (firstSlack n σ) 0 := by
  have hz (i : Fin 7) : ContinuousAt (fun h => Z h i) 0 :=
    (continuous_apply i).continuousAt.comp hZ
  have hm := main_actualRaw_hasDerivAt hZ hZ0 n σ
  have hsecond : ContinuousAt (fun h => actualRaw (1/2+h*Z h 0) (1+h) n σ (Z h 2)) 0 := by
    unfold actualRaw g lagB chebT chebU
    fun_prop
  have hp := parameter_mul_hasDerivAt ((hz 3).mul (hm.continuousAt.sub hsecond))
  have hden : ContinuousAt (fun h : ℝ => lagDenominator (1+h) n) 0 := by
    unfold lagDenominator chebU
    fun_prop
  have hd := parameter_mul_hasDerivAt ((hz 4).mul hden)
  have hf := (hm.sub hp).sub (hd.const_mul σ)
  convert hf using 1
  · funext h
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    unfold rawBranch
    ring
  · dsimp only [Pi.sub_apply,Pi.mul_apply]
    norm_num only [zero_mul,add_zero,hZ0,criticalPoint_3,criticalPoint_4,
      criticalPoint_2,lagDenominator_one n hn]
    have hz0 : actualRaw (1/2) 1 n σ (-(1/2))=0 := by
      simpa only [neg_div] using critical_actualRaw_zero hn hc
    rw [hz0,auxiliary_actualRaw_eq]
    have he := critical_firstDerivative_eq hn hc
    linear_combination -he

/-- Article: the actual raw divided slack converges at every critical lag. -/
theorem tendsto_rawBranch_div {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) {n : ℕ} (hn : 1≤n) {σ : ℝ} (hc : CriticalPair n σ) :
    Tendsto (fun h => rawBranch h (Z h) n σ/h) (𝓝[≠] 0) (𝓝 (firstSlack n σ)) := by
  have ht := (rawBranch_hasDerivAt hZ hZ0 hn hc).tendsto_slope_zero
  have hz : rawBranch 0 (Z 0) n σ=0 := by
    simpa [rawBranch] using critical_actualRaw_zero hn hc
  simpa only [zero_add,hz,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using ht

/-- Article: the actual normalized divided slack converges to sₙ/n. -/
theorem tendsto_actualPrimal_div {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) {n : ℕ} (hn : 1≤n) {σ : ℝ} (hc : CriticalPair n σ) :
    Tendsto (fun h => actualPrimal h (Z h) n σ/h) (𝓝[≠] 0)
      (𝓝 (firstSlack n σ/(n : ℝ))) := by
  have hden : ContinuousAt (fun h : ℝ => lagDenominator (1+h) n) 0 := by
    unfold lagDenominator chebU
    fun_prop
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hd : Tendsto (fun h : ℝ => lagDenominator (1+h) n) (𝓝[≠] 0) (𝓝 (n : ℝ)) := by
    simpa [lagDenominator_one n hn] using hden.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  have hlim := (tendsto_rawBranch_div hZ hZ0 hn hc).div hd hn0
  have hne : ∀ᶠ h in 𝓝[≠] (0 : ℝ), lagDenominator (1+h) n≠0 :=
    hd.eventually (eventually_ne_nhds hn0)
  apply hlim.congr'
  filter_upwards [hne,self_mem_nhdsWithin] with h hne hh
  have hh' : h≠0 := by simpa using hh
  dsimp only [Pi.div_apply]
  have he (a b : ℝ) : (a/lagDenominator (1+h) n-b)/h=
      (a-b*lagDenominator (1+h) n)/h/lagDenominator (1+h) n := by
    field_simp [hne,hh']
  exact he _ _ |>.symm

/-- Article: all critical inactive slacks are positive for small positive h. -/
theorem eventually_actualPrimal_pos_critical {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) {n : ℕ} (hn : 1≤n) {σ : ℝ}
    (hc : CriticalPair n σ) (ha : ¬ActivePair n σ) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0<actualPrimal h (Z h) n σ := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  have hp := div_pos (firstSlack_positive_of_not_active hn hc ha) hnpos
  have ht := (tendsto_actualPrimal_div hZ hZ0 hn hc).mono_left (nhdsGT_le_nhdsNE 0)
  have he := ht.eventually (eventually_gt_nhds hp)
  filter_upwards [he,self_mem_nhdsWithin] with h he hh
  rcases div_pos_iff.mp he with he | he
  · exact he.1
  · exact (not_lt_of_ge (show 0≤h from le_of_lt hh) he.2).elim

/-- Article: every noncritical three-cycle slack is exactly 3/2. -/
theorem noncritical_actualRaw_eq {n : ℕ} (hn : 1≤n) {σ : ℝ} (hs : σ= -1 ∨ σ=1)
    (hc : ¬CriticalPair n σ) : actualRaw (1/2) 1 n σ (-1/2)=3/2 := by
  have hT : chebT n (1 : ℝ)=1 := by simp [chebT]
  unfold actualRaw g lagB
  rw [hT,chebT_cycle,chebU_lag_cycle n hn]
  have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hs with rfl | rfl
  all_goals rcases hmod with hm | hm | hm
  all_goals norm_num [CriticalPair,hm] at hc
  all_goals norm_num [hm]

/-- Article: continuity of every genuine normalized lag through h=0. -/
theorem continuousAt_actualPrimal {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    ContinuousAt (fun h => actualPrimal h (Z h) n σ) 0 := by
  have hz (i : Fin 7) : ContinuousAt (fun h => Z h i) 0 :=
    (continuous_apply i).continuousAt.comp hZ
  have hw : ContinuousAt (fun h =>
      (1-h*Z h 3)*actualRaw (1/2+h*Z h 0) (1+h) n σ (-1/2+h*Z h 1)+
      h*Z h 3*actualRaw (1/2+h*Z h 0) (1+h) n σ (Z h 2)) 0 := by
    unfold actualRaw g lagB chebT chebU
    fun_prop
  have hd : ContinuousAt (fun h : ℝ => lagDenominator (1+h) n) 0 := by
    unfold lagDenominator chebU
    fun_prop
  have hd0 : lagDenominator (1+(0 : ℝ)) n≠0 := by
    simpa [lagDenominator_one n hn] using (show (n : ℝ)≠0 by exact_mod_cast (show n≠0 by omega))
  have hc : ContinuousAt (fun h => σ*h*Z h 4) 0 := by fun_prop
  exact (hw.div hd hd0).sub hc

/-- Article: every noncritical actual lag stays positive near the critical point. -/
theorem eventually_actualPrimal_pos_noncritical {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (_hZ0 : Z 0=criticalPoint) {n : ℕ} (hn : 1≤n) {σ : ℝ}
    (hs : σ= -1 ∨ σ=1) (hc : ¬CriticalPair n σ) :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0<actualPrimal h (Z h) n σ := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  have he : actualPrimal 0 (Z 0) n σ=(3/2)/(n : ℝ) := by
    simp only [actualPrimal,zero_mul,add_zero,sub_zero,one_mul,mul_zero]
    rw [noncritical_actualRaw_eq hn hs hc,lagDenominator_one n hn]
  have hp : 0<actualPrimal 0 (Z 0) n σ := by rw [he]; positivity
  exact (continuousAt_actualPrimal hZ n hn σ).tendsto.eventually (eventually_gt_nhds hp)

end polyak.Boundary.P5
