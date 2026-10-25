import polyak.Global.Sampling.DiscreteMeasure

/-! Even sampled densities give genuine symmetric measures on the circle. -/
noncomputable section
namespace polyak.Global.Sampling
open MeasureTheory

def negSampleIndex {L:ℕ} (j:Fin L) : Fin L :=
  if h:j.val=0 then j else ⟨L-j.val,by omega⟩

theorem negSampleIndex_involutive {L:ℕ} : Function.Involutive (negSampleIndex (L:=L)) := by
  intro j
  apply Fin.ext
  by_cases hj:j.val=0
  · simp only [negSampleIndex,dite_eq_left hj]
  · have hne:L-j.val≠0:=by omega
    simp only [negSampleIndex,dite_eq_right hj,dite_eq_right hne,Fin.val_mk]
    omega

def negSampleEquiv (L:ℕ) : Fin L≃Fin L where
  toFun:=negSampleIndex
  invFun:=negSampleIndex
  left_inv:=negSampleIndex_involutive
  right_inv:=negSampleIndex_involutive

theorem samplePoint_neg {L:ℕ} (hL:0<L) (j:Fin L) :
    samplePoint L (negSampleIndex j)= -samplePoint L j := by
  by_cases hj:j.val=0
  · have he : negSampleIndex j=j:=by simp only [negSampleIndex,dite_eq_left hj]
    rw [he]
    simp only [samplePoint,hj,Nat.cast_zero,mul_zero,zero_div]
    change (0:Circle)= -(0:Circle)
    simp only [neg_zero]
  · simp only [negSampleIndex,dite_eq_right hj,samplePoint]
    have he : 2*Real.pi*((L-j.val:ℕ):ℝ)/L=2*Real.pi-(2*Real.pi*j.val/L) := by
      rw [Nat.cast_sub j.isLt.le]
      field_simp
    rw [he]
    change ((2*Real.pi-(2*Real.pi*j.val/L):ℝ):Circle)= -((2*Real.pi*j.val/L:ℝ):Circle)
    rw [AddCircle.coe_sub,AddCircle.coe_period,zero_sub]

theorem sampleMeasure_symmetric (f:Circle→ℝ) (hf:∀x,f (-x)=f x) {L:ℕ} (hL:0<L) :
    Circle.Symmetric (sampleMeasure f L) := by
  unfold Circle.Symmetric Circle.reflect sampleMeasure
  rw [Measure.map_finset_sum' (by fun_prop)]
  simp only [Measure.map_smul _ (show Measurable (fun x:Circle=>-x) from measurable_neg).aemeasurable,
    Measure.map_dirac]
  conv_rhs => rw [←Equiv.sum_comp (negSampleEquiv L)]
  apply Finset.sum_congr rfl
  intro j _
  change Real.toNNReal (f (samplePoint L j)/(L:ℝ)) • Measure.dirac (-samplePoint L j)=
    Real.toNNReal (f (samplePoint L (negSampleIndex j))/(L:ℝ)) •
      Measure.dirac (samplePoint L (negSampleIndex j))
  rw [samplePoint_neg hL,hf]

end polyak.Global.Sampling
