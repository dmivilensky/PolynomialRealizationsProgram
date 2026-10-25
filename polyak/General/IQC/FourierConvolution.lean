import polyak.General.IQC.FourierShift

/-! Every absolutely summable causal scalar impulse response has its actual
bounded Fourier multiplier. The representation follows from norm-convergent
operator and L-infinity series of the genuine shifts and characters. -/
noncomputable section
namespace polyak.General.IQC.Fourier
open MeasureTheory
open scoped ENNReal
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Unit modulus of every character supplies a uniform essential bound. -/
theorem characterLp_norm_le (n : ℤ) : ‖characterLp n‖≤1 := by
  have hh : ∀ᵐ ω ∂circleMeasure,‖characterLp n ω‖≤(1:ℝ) := by
    filter_upwards [characterLp_ae n] with ω hω
    rw [hω,fourier_apply,Circle.norm_coe]
  simpa only [ENNReal.toReal_top,inv_zero,Real.rpow_zero,one_mul] using
    Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ)≤1) hh

/-- The actual uniformly bounded frequency transfer function in the positive
Fourier convention used by the official AddCircle basis. -/
def transfer (h : ℕ→ℝ) : Lp ℂ ∞ circleMeasure := ∑' n,h n • characterLp (n:ℤ)

theorem transfer_summable {h : ℕ→ℝ} (hh : Summable (fun n=>|h n|)) :
    Summable (fun n=>h n • characterLp (n:ℤ)) := by
  apply hh.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (characterLp_norm_le _)

/-- Norm-convergent whole-line convolution, constructed from actual integer shifts. -/
def wholeConvolution (h : ℕ→ℝ) : ScalarTime→L[ℝ]ScalarTime :=
  ∑' n,h n • zShiftCLM (-(n:ℤ))

theorem wholeConvolution_summable {h : ℕ→ℝ} (hh : Summable (fun n=>|h n|)) :
    Summable (fun n=>h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) := by
  apply hh.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (zShiftCLM_norm_le _)

/-- Dependence of multiplication on its bounded scalar coefficient is continuous linear. -/
def fieldMultiplyAt (x : ScalarFrequency) : Lp ℂ ∞ circleMeasure→L[ℝ]ScalarFrequency :=
  (((ContinuousLinearMap.apply ℝ ℂ).flip.holderL circleMeasure ∞ 2 2).flip x).comp
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ→L[ℝ](ℂ→L[ℝ]ℂ)).compLpL ∞ circleMeasure)

@[simp] theorem fieldMultiplyAt_apply (x : ScalarFrequency) (p : Lp ℂ ∞ circleMeasure) :
    fieldMultiplyAt x p=multiply (scalarOperator p) x := rfl

@[simp] theorem fieldMultiplyAt_character (x : ScalarFrequency) (n : ℤ) :
    fieldMultiplyAt x (characterLp n)=mulCharacter n x := rfl

private theorem convolution_transform_term (h : ℕ→ℝ) (x : ScalarTime) (n : ℕ) :
    scalarUnitary ((h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) x)=
      fieldMultiplyAt (scalarUnitary x) (h n • characterLp (n:ℤ)) := by
  change scalarUnitary (h n • zShift (-(n:ℤ)) x)=_
  rw [scalarUnitary.map_smul,scalarUnitary_shift,neg_neg]
  rw [(fieldMultiplyAt (scalarUnitary x)).map_smul,fieldMultiplyAt_character]

/-- Fourier diagonalization of every l1 impulse response, without a representation hypothesis. -/
theorem wholeConvolution_transform {h : ℕ→ℝ} (hh : Summable (fun n=>|h n|)) (x : ScalarTime) :
    scalarUnitary (wholeConvolution h x)=multiply (scalarOperator (transfer h)) (scalarUnitary x) := by
  have ht := (ContinuousLinearMap.apply ℝ ScalarTime x).hasSum (wholeConvolution_summable hh).hasSum
  change HasSum (fun n : ℕ=>(h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) x) (wholeConvolution h x) at ht
  have hU := scalarUnitary.toContinuousLinearEquiv.toContinuousLinearMap.hasSum ht
  change HasSum (fun n : ℕ=>scalarUnitary ((h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) x))
    (scalarUnitary (wholeConvolution h x)) at hU
  simp only [convolution_transform_term] at hU
  have hf := (fieldMultiplyAt (scalarUnitary x)).hasSum (transfer_summable hh).hasSum
  change HasSum (fun n : ℕ=>fieldMultiplyAt (scalarUnitary x) (h n • characterLp (n:ℤ)))
    (fieldMultiplyAt (scalarUnitary x) (transfer h)) at hf
  exact hU.unique hf

/-- Pointwise evaluation of the genuine whole-line convolution. -/
theorem wholeConvolution_apply {h : ℕ→ℝ} (hh : Summable (fun n=>|h n|))
    (x : ScalarTime) (k : ℤ) : wholeConvolution h x k=∑' n,h n • x (k-(n:ℤ)) := by
  have hs := wholeConvolution_summable hh
  have he := (ContinuousLinearMap.apply ℝ ScalarTime x).map_tsum hs
  change wholeConvolution h x=∑' n,(h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) x at he
  rw [he]
  have hev := (lp.evalCLM ℝ (fun _ : ℤ=>ℂ) 2 k).map_tsum
    ((ContinuousLinearMap.apply ℝ ScalarTime x).summable hs)
  change (∑' n,(h n • zShiftCLM (E:=ℂ) (-(n:ℤ))) x) k=_ at hev
  rw [hev]
  apply tsum_congr
  intro n
  change h n • x (k+ -(n:ℤ))=h n • x (k-(n:ℤ))
  rw [sub_eq_add_neg]

/-- Zero extension commutes with the actual causal finite-prefix convolution. -/
theorem zeroExtend_convolution {h : ℕ→ℝ} (hh : Summable (fun n=>|h n|))
    (x : SequenceSpace ℂ) (k : ℤ) :
    wholeConvolution h (zeroExtendL2 x) k=zeroExtend (convolution h (fun n=>x n)) k := by
  rw [wholeConvolution_apply hh]
  by_cases hk : 0≤k
  · let N := k.toNat
    have hcast : (N:ℤ)=k := Int.toNat_of_nonneg hk
    have he : (∑' n,h n • zeroExtendL2 x (k-(n:ℤ)))=
        ∑ n∈Finset.range (N+1),h n • zeroExtendL2 x (k-(n:ℤ)) := by
      apply tsum_eq_sum
      intro n hn
      have hnN : N<n := by simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hn
      have hneg : k-(n:ℤ)<0 := by omega
      rw [zeroExtendL2_apply,zeroExtend_neg (fun n=>x n) hneg,smul_zero]
    rw [he]
    rw [zeroExtend,ite_eq_left hk]
    change _=∑ n∈Finset.range (N+1),h n • delay n (fun n=>x n) N
    apply Finset.sum_congr rfl
    intro n hn
    apply congrArg (fun a : ℂ=>h n • a)
    have hnN : n≤N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [zeroExtendL2_apply,zeroExtend,ite_eq_left (by omega),delay,ite_eq_left hnN]
    have heNat : (k-(n:ℤ)).toNat=N-n := by omega
    rw [heNat]
  · have hzero : ∀ n : ℕ,zeroExtendL2 x (k-(n:ℤ))=0 := by
      intro n
      rw [zeroExtendL2_apply,zeroExtend_neg (fun n=>x n) (by omega)]
    simp only [hzero,smul_zero,tsum_zero,zeroExtend,hk,ite_false]

/-- The actual causal Feedback plant is diagonalized by the canonical half-line Fourier transform. -/
theorem halfLine_plant_transform (F : Feedback ℂ) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (x : SequenceSpace ℂ) :
    halfLineTransform (F.plantL2 x)=multiply (scalarOperator (transfer h)) (halfLineTransform x) := by
  have he : zeroExtendL2 (F.plantL2 x)=wholeConvolution h (zeroExtendL2 x) := by
    ext k
    rw [zeroExtend_convolution hh]
    change zeroExtend (fun n=>F.plant x n) k=zeroExtend (convolution h x) k
    rw [hF]
  change scalarUnitary (zeroExtendL2 (F.plantL2 x))=_
  rw [he,wholeConvolution_transform hh]
  rfl

end polyak.General.IQC.Fourier
