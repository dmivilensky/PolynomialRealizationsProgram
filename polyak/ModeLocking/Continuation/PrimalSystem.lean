import polyak.ModeLocking.Continuation.Transversality
import polyak.ModeLocking.Continuation.WeightedDerivative

/-! The actual analytic system whose unknowns are the shift and the
normalized primal masses. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels
open scoped BigOperators

abbrev Parameters := Fin 3 → ℝ
def parameters (q : Tuning) : Parameters := ![q.kappa, q.y, q.beta]

def systemPoint {d : ℕ} (z : Parameters × (ℝ × (Fin d → ℝ))) : SourcePoint :=
  ![z.1 0, z.1 1, z.1 2, z.2.1]

def primalSystem {d : ℕ} (r : Fin d → ℤ) (a : Fin d → Frequency)
    (z : Parameters × (ℝ × (Fin d → ℝ))) : (Fin d → ℝ) × ℝ :=
  ((tightMatrix r a (systemPoint z)).mulVec z.2.2, (∑ i, z.2.2 i) - 1)

theorem analyticAt_systemPoint {d : ℕ} (z : Parameters × (ℝ × (Fin d → ℝ))) :
    AnalyticAt ℝ (@systemPoint d) z := by
  have hc (i : Fin 3) : AnalyticAt ℝ (fun p : Parameters × (ℝ × (Fin d → ℝ)) => p.1 i) z :=
    ((ContinuousLinearMap.proj (R := ℝ) i : Parameters →L[ℝ] ℝ).analyticAt z.1).comp analyticAt_fst
  have hs : AnalyticAt ℝ (fun p : Parameters × (ℝ × (Fin d → ℝ)) => p.2.1) z :=
    analyticAt_fst.comp analyticAt_snd
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hs

theorem analyticAt_primalSystem (q : Tuning) (s : ℝ) {d : ℕ} (r : Fin d → ℤ)
    (a : Fin d → Frequency) (w : Fin d → ℝ) :
    AnalyticAt ℝ (primalSystem r a) (parameters q, s, w) := by
  have hinput := analyticAt_systemPoint (parameters q, s, w)
  have hlag (i j : Fin d) : AnalyticAt ℝ
      (fun z : Parameters × (ℝ × (Fin d → ℝ)) => ambientLag (r i) (a j) (systemPoint z))
      (parameters q, s, w) := by
    have hout : AnalyticAt ℝ (ambientLag (r i) (a j)) (systemPoint (parameters q, s, w)) :=
      analyticAt_ambientLag q s (r i) (a j)
    exact hout.comp (f := @systemPoint d) hinput
  have hw (i : Fin d) : AnalyticAt ℝ
      (fun z : Parameters × (ℝ × (Fin d → ℝ)) => z.2.2 i) (parameters q, s, w) := by
    have hin : AnalyticAt ℝ (fun z : Parameters × (ℝ × (Fin d → ℝ)) => z.2.2) (parameters q, s, w) :=
      analyticAt_snd.comp analyticAt_snd
    exact ((ContinuousLinearMap.proj (R := ℝ) i : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt w).comp
      (f := fun z : Parameters × (ℝ × (Fin d → ℝ)) => z.2.2) hin
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro i
    exact Finset.analyticAt_fun_sum Finset.univ (fun j _ => (hlag i j).mul (hw j))
  · exact (Finset.analyticAt_fun_sum Finset.univ (fun i _ => hw i)).sub analyticAt_const

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem primalSystem_base : Continuation.primalSystem D.reps D.atoms
    (Continuation.parameters q, s, fun i => (D.primal i : ℝ)) = 0 := by
  apply Prod.ext
  · change (Continuation.tightMatrix D.reps D.atoms (Continuation.sourcePoint q s)).mulVec
      (fun i => (D.primal i : ℝ)) = 0
    have he : Continuation.tightMatrix D.reps D.atoms (Continuation.sourcePoint q s) = D.matrix := by
      ext i j
      exact Continuation.ambientLag_actual q s (D.reps i) (D.atoms j)
    rw [he]
    exact D.matrix_mul_primal
  · change (∑ i, (D.primal i : ℝ)) - 1 = 0
    have hnorm : (∑ i, (D.primal i : ℝ)) = 1 := by exact_mod_cast D.primal_sum
    rw [hnorm, sub_self]

end polyak.ModeLocking.RegularData
