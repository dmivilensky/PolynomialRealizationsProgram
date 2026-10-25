import polyak.Regularity.Critical
import polyak.Spiral.Feasibility

/-!
Article: Proposition spiralsub and the exact spiral-equality set.
Use: the actual rate equals the spiral precisely when the spiral attains the
actual boundary at T. A strict boundary improvement at the spiral exponent
therefore forces a strictly larger original rate.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Regularity

theorem actual_factor_eq_spiral_iff_boundary {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    Real.exp (T q)=Spiral.factor q ↔ V (T q)=Real.arsinh (Spiral.twist (T q)) := by
  have hactual := T_sub_log_eq_V hq hq1
  constructor
  · intro he
    have hz : Spiral.spiralPolynomial (Real.exp (T q)) q=0 := by
      rw [he]
      exact (Spiral.factor_spec hq hq1).2
    have ht := (Spiral.actual_relation_iff hq (T q)).mpr hz
    rw [hactual] at ht
    rw [ht,Real.arsinh_sinh]
  · intro he
    have ht : Spiral.twist (T q)=Real.sinh (T q-Real.log q) := by
      rw [hactual,he,Real.sinh_arsinh]
    have hz := (Spiral.actual_relation_iff hq (T q)).mp ht
    exact (Spiral.existsUnique_spiral_root hq hq1).unique
      ⟨Real.exp_pos _,hz⟩ (Spiral.factor_spec hq hq1)

theorem spiral_lt_actual_of_boundary_improvement {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (himprove : Real.arsinh (Spiral.twist (Real.log (Spiral.factor q)))<
      V (Real.log (Spiral.factor q))) : Spiral.factor q<Real.exp (T q) := by
  have hle : Real.log (Spiral.factor q)≤T q :=
    (isGreatest_T hq).2 ⟨_,_,Spiral.actual_feasible hq hq1⟩
  have hne : Real.log (Spiral.factor q)≠T q := by
    intro he
    have hfactor : Real.exp (T q)=Spiral.factor q := by
      rw [←he,Real.exp_log (Spiral.factor_spec hq hq1).1]
    have hb := (actual_factor_eq_spiral_iff_boundary hq hq1).mp hfactor
    rw [he,hb] at himprove
    exact (lt_irrefl _ himprove)
  have hlt := Real.exp_lt_exp.mpr (lt_of_le_of_ne hle hne)
  rwa [Real.exp_log (Spiral.factor_spec hq hq1).1] at hlt

end polyak.Boundary
