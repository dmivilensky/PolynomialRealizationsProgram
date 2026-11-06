import nesterov.Spread.Hyperbolic

/-! A uniform tail for every measure on a half-step band. -/
namespace nesterov.Spread
noncomputable section
open Filter Spectral
open scoped Topology

theorem lowerPoint_extreme (a : SymbolPair) {t : ℝ} (ht : t<0) (η : ℝ)
    (n : ℕ) (c : Frequency) :
    lowerPoint a t η n c=g a c*ePlus η (n*|t|)-lowerOsc a n c := by
  unfold lowerPoint lagA lagB ePlus lowerOsc
  rw [abs_of_neg ht,mul_neg,Real.cosh_neg,Real.sinh_neg]
  ring

theorem upperPoint_extreme (a : SymbolPair) {t : ℝ} (ht : t<0) (η : ℝ)
    (n : ℕ) (c : Frequency) :
    upperPoint a t η n c=g a c*eMinus η (n*|t|)-upperOsc a n c := by
  unfold upperPoint lagA lagB eMinus upperOsc
  rw [abs_of_neg ht,mul_neg,Real.cosh_neg,Real.sinh_neg]
  ring

theorem exists_uniform_tail {t η : ℝ} (ht : t<0) (hη : 0<η) (hη1 : η<1) :
    ∃ N : ℕ,∀ n : ℕ,N≤n →
      4<eMinus η (n*|t|) ∧ 4<ePlus η (n*|t|) := by
  have htpos : 0 < |t| := abs_pos.mpr ht.ne
  have hn : Tendsto (fun n : ℕ=>(n:ℝ)*|t|) atTop atTop :=
    Tendsto.atTop_mul_const htpos tendsto_natCast_atTop_atTop
  have hex : Tendsto (fun n : ℕ=>(η/2)*Real.exp ((n:ℝ)*|t|)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hn).const_mul_atTop (by linarith : 0<η/2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hex.eventually_gt_atTop 4)
  refine ⟨N,fun n hn=>?_⟩
  have hx : 0≤(n:ℝ)*|t| := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hm := (hN n hn).trans_le (eMinus_ge_growing_exp hη.le hη1.le)
  exact ⟨hm,hm.trans_le (ePlus_ge_eMinus hη1.le hx)⟩

theorem points_positive_of_tail (a : SymbolPair) {t η : ℝ} (ht : t<0)
    {n : ℕ} (hm : 4<eMinus η (n*|t|)) (hp : 4<ePlus η (n*|t|))
    (c : Frequency) (hg : 0<g a c)
    (hl : lowerOsc a n c≤4*g a c) (hu : upperOsc a n c≤4*g a c) :
    0<lowerPoint a t η n c ∧ 0<upperPoint a t η n c := by
  rw [lowerPoint_extreme a ht,upperPoint_extreme a ht]
  constructor
  · nlinarith [mul_pos hg (sub_pos.mpr hp)]
  · nlinarith [mul_pos hg (sub_pos.mpr hm)]

end
end nesterov.Spread
