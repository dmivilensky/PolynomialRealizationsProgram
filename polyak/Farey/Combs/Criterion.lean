import polyak.Farey.Combs.Actual
import polyak.Farey.Records.Selection

/-! Every admissible two-atom ratio, at both closed endpoints. Lag
feasibility and the additional minimizer inequality are distinct statements. -/
noncomputable section
namespace polyak.Farey
open Levels MeasureTheory

def CombData.lowerRatio (d : CombData) : ℝ :=
  lowerMassRatio d.positions d.anchorColumn d.companionColumn d.anchor_negative_nonempty

def CombData.upperRatio (d : CombData) : ℝ :=
  upperMassRatio d.positions d.anchorColumn d.companionColumn d.companion_negative_nonempty

theorem Comb.lag_feasible_iff {Θ : Curve} (C : Comb Θ) :
    (∃w0 wc : ℝ,0 < w0 ∧ 0 < wc ∧ ∀n : ℤ,
      0≤w0*Θ.lag n C.data.anchorFrequency+wc*Θ.lag n C.data.companionFrequency) ↔
    C.data.Selection ∧ C.data.lowerRatio≤C.data.upperRatio := by
  have hh := two_columns_exists_iff C.data.positions C.data.anchorColumn C.data.companionColumn
    C.data.anchor_negative_nonempty C.data.companion_negative_nonempty
  simpa only [C.all_lags_iff,←C.data.selection_iff,CombData.lowerRatio,CombData.upperRatio] using hh

theorem Comb.mass_ratio_iff {Θ : Curve} (C : Comb Θ) {w0 wc : ℝ}
    (hw0 : 0 < w0) (hwc : 0 < wc) :
    (∀n : ℤ,0≤w0*Θ.lag n C.data.anchorFrequency+wc*Θ.lag n C.data.companionFrequency) ↔
    C.data.Selection ∧ C.data.lowerRatio≤wc/w0 ∧ wc/w0≤C.data.upperRatio := by
  rw [C.all_lags_iff]
  simpa only [←C.data.selection_iff,CombData.lowerRatio,CombData.upperRatio] using
    two_columns_mass_ratio_iff C.data.positions C.data.anchorColumn C.data.companionColumn
      C.data.anchor_negative_nonempty C.data.companion_negative_nonempty hw0 hwc

theorem Comb.twoatom_criterion {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal)
    (hw0 : 0 < w0) (hwc : 0 < wc) :
    ProgramSolution Θ nonzeroLags (C.measure w0 wc) ↔
      (C.data.Selection ∧ C.data.lowerRatio≤(wc:ℝ)/(w0:ℝ) ∧ (wc:ℝ)/(w0:ℝ)≤C.data.upperRatio) ∧
      0≤(w0:ℝ)*Real.cos (Θ C.data.anchorFrequency)+(wc:ℝ)*Real.cos (Θ C.data.companionFrequency) := by
  rw [C.program_iff w0 wc hw0 hwc]
  have hh := C.mass_ratio_iff (show (0:ℝ) < w0 by exact_mod_cast hw0)
    (show (0:ℝ) < wc by exact_mod_cast hwc)
  rw [C.all_lags_iff] at hh
  rw [hh]
  exact and_comm

def CombData.auxiliaryNumerator (d : CombData) : ℤ := (d.j*d.τ-d.i)/d.k

theorem CombData.auxiliary_identity (d : CombData) :
    d.j*d.τ=d.auxiliaryNumerator*d.k+d.i := by
  have hd : d.k∣d.j*d.τ-d.i := by
    convert dvd_neg.mpr d.transport using 1
    ring
  have hh := Int.ediv_mul_cancel hd
  change d.auxiliaryNumerator*d.k=d.j*d.τ-d.i at hh
  linarith

theorem CombData.full_selection_iff (d : CombData) (ht : d.t=d.j) :
    d.Selection ↔ Int.gcd d.auxiliaryNumerator d.j=1 ∧
      ∃R : RightParent d.auxiliaryNumerator d.j,d.i*R.den < d.k ∧
        d.ac < ((d.k:ℝ)+(R.leftDen:ℝ)*(d.i:ℝ))/(d.j:ℝ) := by
  have hh := record_selection_iff d.j_ge d.i_pos
    (show d.i < d.k by have h:=d.i_half;have h':=d.i_pos;omega)
    d.auxiliary_identity d.companion_out
  simpa only [CombData.Selection,RecordSelection,ht] using hh

theorem CombData.shallow_selection (d : CombData)
    (h : RecordSelection d.k d.j d.τ d.ac) : d.Selection :=
  record_selection_shallow d.t_le h

end polyak.Farey
