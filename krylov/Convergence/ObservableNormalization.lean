import krylov.Convergence.ObservableStep
import krylov.Convergence.WindowNormalization
import krylov.Methods.ChronologicalWindow
import krylov.Functions.MetricSearchOperator

/-!
Article: main_krylov, apG:Dunif, actual coefficient inverse domains.
Use: transfer a derived normalized cross-Gram domain to the original
physical newest-first stored solve, with every matrix explicitly identified.
Source: exact real primal/dual pairings, diagonal congruence and simultaneous
finite reindexing of the true determinant.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A true normalized solve domain proves the original raw domain;
even individual normalization domains are unnecessary for this implication.
Article: main_krylov, apG:Dunif. -/
theorem observable_raw_unit_of_normalized (s y : Fin p → E)
    (hu : IsUnit (crossGram (unitWindowImages s y) (unitWindow s)).det) :
    IsUnit (crossGram y s).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply isUnit_iff_ne_zero.mp hu
  change (crossGram (rescaleWindow y (fun i=>‖s i‖⁻¹))
    (rescaleWindow s (fun i=>‖s i‖⁻¹))).det=0
  rw [window_crossGram_rescale,rescaleModel,det_mul,det_mul,hz,mul_zero,zero_mul]

/-- The real primal/dual metric arrays have exactly the original
physical observed cross-Gram, without changing the algorithm.
Article: main_krylov, apG:Dunif. -/
theorem observable_metric_crossGram (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) :
    crossGram (fun i=>T.symm (y i)) (fun i=>T (s i))=crossGram y s := by
  ext i j
  change inner ℝ (T.symm (y i)) (T (s j))=inner ℝ (y i) (s j)
  rw [real_inner_comm,metric_primal_dual_pairing T hT,real_inner_comm]

/-- The literal complete newest-first observed determinant equals its
genuine chronological array determinant. Article: apG:Dunif. -/
theorem observable_executed_det_chronological (s y : ℕ → E) (k : ℕ) :
    (crossGram (windowImages (executedPairs s y k)) (windowSteps (executedPairs s y k))).det=
      (crossGram (fun i : Fin k=>y i.val) (fun i : Fin k=>s i.val)).det := by
  rw [crossGram_executed_det]
  have he (i : Fin k) : k-1-i.val=(Fin.revPerm i).val := by
    simp only [Fin.revPerm_apply,Fin.rev,Fin.val_mk]
    omega
  have hm : crossGram (fun i : Fin k=>y (k-1-i.val)) (fun i : Fin k=>s (k-1-i.val))=
      (crossGram (fun i : Fin k=>y i.val) (fun i : Fin k=>s i.val)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [crossGram,Matrix.submatrix,he]
    rfl
  rw [hm,Matrix.det_submatrix_equiv_self]

end
end krylov.Convergence
