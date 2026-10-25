import polyak.ModeLocking.Continuation.Data
import polyak.ModeLocking.Regular.Endpoints

/-! A single literal joint symbol on original source coordinates and real
frequency. Its analyticity is proved along the whole closed base interval. -/
noncomputable section
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

def jointPoint (z : Continuation.Parameters × ℝ) : Chart.AmbientPoint :=
  ![z.1 0, z.1 1, z.1 2, C.shift z.1, z.2]

def jointSymbol (z : Continuation.Parameters × ℝ) : ℝ :=
  ∑ n ∈ D.lags, C.weight z.1 n * Continuation.jointLag n (C.jointPoint z)

theorem shift_base : C.shift (Continuation.parameters q) = s :=
  congrArg Prod.fst C.primalShift_base

theorem jointPoint_base (x : ℝ) : C.jointPoint (Continuation.parameters q, x) =
    ![q.kappa, q.y, q.beta, s, x] := by
  unfold jointPoint
  rw [C.shift_base]
  rfl

theorem jointSymbol_base (x : ℝ) : C.jointSymbol (Continuation.parameters q, x) =
    finiteSymbol q s D.lags D.dual x := by
  unfold jointSymbol
  simp only [C.weight_base, C.jointPoint_base]
  rfl

theorem jointSymbol_actual (q' : Tuning) (x : ℝ) :
    C.jointSymbol (Continuation.parameters q', x) =
      finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags
        (C.weight (Continuation.parameters q')) x := rfl

theorem analyticAt_jointSymbol {x : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) :
    AnalyticAt ℝ C.jointSymbol (Continuation.parameters q, x) := by
  have hfst : AnalyticAt ℝ (fun z : Continuation.Parameters × ℝ => z.1)
      (Continuation.parameters q, x) := analyticAt_fst
  have hshift : AnalyticAt ℝ C.shift (Continuation.parameters q) :=
    analyticAt_fst.comp (f := C.primalShift) C.analytic_primalShift
  have hs : AnalyticAt ℝ (fun z : Continuation.Parameters × ℝ => C.shift z.1)
      (Continuation.parameters q, x) :=
    hshift.comp (g := C.shift) (f := fun z : Continuation.Parameters × ℝ => z.1) hfst
  have hcoord (i : Fin 3) : AnalyticAt ℝ (fun z : Continuation.Parameters × ℝ => z.1 i)
      (Continuation.parameters q, x) := by
    have hc : AnalyticAt ℝ (fun p : Continuation.Parameters => p i) (Continuation.parameters q) :=
      (ContinuousLinearMap.proj (R := ℝ) i : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
    exact hc.comp (f := fun z : Continuation.Parameters × ℝ => z.1) hfst
  have hp : AnalyticAt ℝ C.jointPoint (Continuation.parameters q, x) := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hcoord 0
    · exact hcoord 1
    · exact hcoord 2
    · exact hs
    · exact analyticAt_snd
  unfold jointSymbol
  apply Finset.analyticAt_fun_sum
  intro n _
  have hn : AnalyticAt ℝ (Continuation.jointLag n) (C.jointPoint (Continuation.parameters q, x)) := by
    rw [C.jointPoint_base]
    exact Continuation.analyticAt_jointLag q s n hx
  exact ((C.analytic_weight n).comp (f := fun z : Continuation.Parameters × ℝ => z.1) hfst).mul (hn.comp hp)

theorem jointSymbol_zero (q' : Tuning) : C.jointSymbol (Continuation.parameters q', 0) = 0 := by
  rw [C.jointSymbol_actual]
  change finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags
    (C.weight (Continuation.parameters q')) (frequencyZero : ℝ) = 0
  rw [finiteSymbol_actual]
  simp only [Curve.lag_at_zero, mul_zero, Finset.sum_const_zero]

theorem jointSymbol_slope_zero (q' : Tuning) :
    deriv (fun x => C.jointSymbol (Continuation.parameters q', x)) 0 = 0 := by
  change deriv (finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags
    (C.weight (Continuation.parameters q'))) 0 = 0
  exact finiteSymbol_deriv_zero q' _ _ _

end polyak.ModeLocking.RegularData.ContinuationData
