import polyak.Levels.Program.Curve
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.Convolution

/-! The literal circle, reflection, and folding for periodic sampling. -/
noncomputable section
namespace polyak.Global
open MeasureTheory Set
open scoped NNReal ENNReal

abbrev Circle := AddCircle (2*Real.pi)

namespace Circle
instance periodPositive : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

def ofReal : ℝ→+Circle := QuotientAddGroup.mk' _

@[fun_prop] theorem continuous_ofReal : Continuous ofReal := AddCircle.continuous_mk' _

@[simp] theorem ofReal_add (x y:ℝ) : ofReal (x+y)=ofReal x+ofReal y := map_add _ _ _
@[simp] theorem ofReal_neg (x:ℝ) : ofReal (-x) = -ofReal x := map_neg _ _

abbrev haar : Measure Circle := AddCircle.haarAddCircle

def reflect (μ : Measure Circle) : Measure Circle := μ.map (fun x=>-x)

def Symmetric (μ : Measure Circle) : Prop := reflect μ=μ

def embed (ω : Levels.Frequency) : Circle := ofReal ω

@[fun_prop] theorem continuous_embed : Continuous embed := continuous_ofReal.comp continuous_subtype_val

def symmetrize (w : Measure Levels.Frequency) : Measure Circle :=
  (1/2:ℝ≥0∞) • (w.map embed+reflect (w.map embed))

theorem reflect_reflect (μ : Measure Circle) : reflect (reflect μ)=μ := by
  rw [reflect,reflect,Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,neg_neg,Measure.map_id']

theorem reflect_symmetrize (w : Measure Levels.Frequency) : Symmetric (symmetrize w) := by
  unfold Symmetric symmetrize
  have hm : Measurable (fun x : Circle=>-x) := continuous_neg.measurable
  change ((1/2:ℝ≥0∞) • (w.map embed+reflect (w.map embed))).map (fun x=>-x)=_
  rw [Measure.map_smul _ hm.aemeasurable,Measure.map_add _ _ hm]
  change (1/2:ℝ≥0∞) • (reflect (w.map embed)+reflect (reflect (w.map embed)))=_
  rw [reflect_reflect,add_comm]

end Circle
end polyak.Global
