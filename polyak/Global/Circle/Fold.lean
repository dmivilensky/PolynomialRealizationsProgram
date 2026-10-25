import polyak.Global.Circle.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Exact folding to the closed half-circle, including both fixed points. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set
open scoped ENNReal NNReal

def fold (x : Circle) : Levels.Frequency :=
  ⟨Real.arccos ((AddCircle.toCircle x:ℂ).re),Real.arccos_nonneg _,Real.arccos_le_pi _⟩

@[fun_prop] theorem continuous_fold : Continuous fold := by
  apply Continuous.subtype_mk
  exact Real.continuous_arccos.comp
    (Complex.continuous_re.comp (_root_.continuous_subtype_val.comp AddCircle.continuous_toCircle))

@[simp] theorem fold_neg (x : Circle) : fold (-x)=fold x := by
  apply Subtype.ext
  simp only [fold,AddCircle.toCircle_neg,_root_.Circle.coe_inv_eq_conj,Complex.conj_re]

theorem toCircle_ofReal (x : ℝ) : (AddCircle.toCircle (ofReal x):ℂ)=Complex.exp ((x:ℂ)*Complex.I) := by
  change (AddCircle.toCircle (x:Circle):ℂ)=_
  rw [AddCircle.toCircle_apply_mk,_root_.Circle.coe_exp]
  congr 2
  field_simp

@[simp] theorem fold_embed (ω : Levels.Frequency) : fold (embed ω)=ω := by
  apply Subtype.ext
  change Real.arccos ((AddCircle.toCircle (ofReal ω):ℂ).re)=_
  rw [toCircle_ofReal,Complex.exp_ofReal_mul_I_re]
  exact Real.arccos_cos ω.property.1 ω.property.2

@[simp] theorem fold_reflect_embed (ω : Levels.Frequency) : fold (-embed ω)=ω := by
  rw [fold_neg,fold_embed]

def folded (μ : Measure Circle) : Measure Levels.Frequency := μ.map fold

@[simp] theorem fold_symmetrize (w : Measure Levels.Frequency) : folded (symmetrize w)=w := by
  unfold folded symmetrize
  have hf : Measurable fold := continuous_fold.measurable
  have he : Measurable embed := continuous_embed.measurable
  have hn : Measurable (fun x : Circle=>-x) := continuous_neg.measurable
  rw [Measure.map_smul _ hf.aemeasurable,Measure.map_add _ _ hf,
    Measure.map_map hf he]
  change (1/2:ℝ≥0∞) • (Measure.map (fold∘embed) w+
    Measure.map fold (Measure.map (fun x=>-x) (Measure.map embed w)))=w
  rw [Measure.map_map hf hn,Measure.map_map (hf.comp hn) he]
  have h₁ : fold∘embed=id := funext fold_embed
  have h₂ : (fold∘fun x=>-x)∘embed=id := funext fold_reflect_embed
  rw [h₁,h₂,Measure.map_id,←two_smul ℝ≥0∞ w,smul_smul]
  rw [one_div,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_smul]

end polyak.Global.Circle
