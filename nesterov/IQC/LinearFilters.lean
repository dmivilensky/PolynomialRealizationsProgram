import polyak.General.IQC.KernelL2
import polyak.Energy.KernelSize
import nesterov.IQC.StationaryResponse

/-! Actual finite polynomial filters on the whole-line Hilbert sequence space. -/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def filterCLM (L : LinearFilter) : ZSpace E→L[ℝ]ZSpace E :=
  (L.map fun p=>p.1 • zShiftCLM p.2).sum

@[simp] theorem filterCLM_apply (L : LinearFilter) (x : ZSpace E) (k : ℤ) :
    filterCLM L x k=filterEval L (fun j=>x j) k := by
  induction L with
  | nil=>rfl
  | cons p L ih=>
    change (p.1 • zShiftCLM (E:=E) p.2+filterCLM (E:=E) L) x k=_
    simp only [add_apply,smul_apply,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,
      Pi.smul_apply,zShiftCLM_apply,ih,filterEval,List.map_cons,List.sum_cons]

theorem filterCLM_bound (L : LinearFilter) (x : ZSpace E) :
    ‖filterCLM L x‖≤filterSize L*‖x‖ := by
  induction L with
  | nil=>simp [filterCLM,filterSize]
  | cons p L ih=>
    change ‖(p.1 • zShiftCLM (E:=E) p.2+filterCLM (E:=E) L) x‖≤_
    calc
      _≤‖p.1 • zShift p.2 x‖+‖filterCLM L x‖:=norm_add_le _ _
      _≤|p.1| *‖x‖+filterSize L*‖x‖:=by
        rw [norm_smul,Real.norm_eq_abs,zShift_norm]
        exact add_le_add_right ih _
      _=filterSize (p::L)*‖x‖:=by simp [filterSize]; ring

/-- Coefficients in ascending order become genuine integer-forward shifts. -/
def coefficientFilter {d : ℕ} (v : Fin d→ℝ) : LinearFilter :=
  List.ofFn (fun j=>(v j,(j.val:ℤ)))

@[simp] theorem filterEval_coefficientFilter {d : ℕ} (v : Fin d→ℝ)
    (x : ℤ→E) (k : ℤ) : filterEval (coefficientFilter v) x k=
      ∑ j,v j • x (k+j.val) := by
  simp [filterEval,coefficientFilter,List.sum_ofFn]

@[simp] theorem filterSize_coefficientFilter {d : ℕ} (v : Fin d→ℝ) :
    filterSize (coefficientFilter v)=∑ j,|v j| := by
  simp [filterSize,coefficientFilter,List.sum_ofFn]

end
end nesterov.IQC
