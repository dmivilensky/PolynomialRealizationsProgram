import polyak.ModeLocking.Regular.Definitions
import polyak.Global.Symbols.Slackness
import polyak.Global.Symbols.Normalized
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The value and slope equalities on the support are consequences of the
primary regularity conditions. They are not extra assumptions. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set Filter
open scoped BigOperators Topology

theorem analyticAt_lagExtension (q : Tuning) (s : ℝ) (n : ℤ) {x : ℝ}
    (hx : x ∈ Icc 0 Real.pi) : AnalyticAt ℝ (lagExtension q s n) x := by
  have hp : AnalyticAt ℝ (fun y : ℝ => ![q.kappa, q.y, q.beta, s, y]) x := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    all_goals first | exact analyticAt_const | exact analyticAt_id
  have ht := (Geometry.analyticAt_jointAngle_actual q s hx).comp (f := fun y : ℝ => ![q.kappa, q.y, q.beta, s, y]) hp
  exact (Real.analyticAt_cos.comp ht).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.mul analyticAt_id).sub ht))

theorem analyticAt_finiteSymbol (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ)
    {x : ℝ} (hx : x ∈ Icc 0 Real.pi) : AnalyticAt ℝ (finiteSymbol q s N a) x := by
  exact N.analyticAt_fun_sum (fun n _ => (analyticAt_const (v := a n)).mul (analyticAt_lagExtension q s n hx))

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem symbol_zero_endpoint : finiteSymbol q s D.lags D.dual 0 = 0 := by
  change finiteSymbol q s D.lags D.dual (frequencyZero : ℝ) = 0
  rw [finiteSymbol_actual]
  simp only [Curve.lag_at_zero, mul_zero, Finset.sum_const_zero]

theorem symbol_nonpos (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
    finiteSymbol q s D.lags D.dual x ≤ 0 := by
  classical
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, D.symbol_zero_endpoint]
  rcases eq_or_lt_of_le hx.2 with hpi | hpi
  · exact (D.dual_strict x h0 hx.2 (fun i hi => D.atoms_lt_pi i |>.ne (hi.symm.trans hpi))).le
  by_contra hn
  have hp : 0 < finiteSymbol q s D.lags D.dual x := lt_of_not_ge hn
  have hd : Dense (range (fun i => (D.atoms i : ℝ)))ᶜ :=
    (finite_range _).countable.dense_compl ℝ
  have hnb : {y | 0 < y ∧ y < Real.pi ∧ 0 < finiteSymbol q s D.lags D.dual y} ∈ 𝓝 x := by
    filter_upwards [Ioo_mem_nhds h0 hpi,
      (analyticAt_finiteSymbol q s D.lags D.dual hx).continuousAt.eventually
        (eventually_gt_nhds hp)] with y hy hz
    exact ⟨hy.1, hy.2, hz⟩
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hnb
  obtain ⟨y, hy, hyU⟩ := hd.exists_mem_open hUopen ⟨x, hxU⟩
  have hyb := hUsub hyU
  have hstrict := D.dual_strict y hyb.1 hyb.2.1.le (fun i hi => hy ⟨i, hi.symm⟩)
  linarith [hyb.2.2]

theorem lag_tight (n : ℤ) (hn : n ∈ D.lags) :
    ∑ i, (D.primal i : ℝ) * (Geometry.shiftedCurve q s).lag n (D.atoms i) = 0 := by
  rcases D.classes n hn with hz | ⟨r, hr⟩
  · simp only [fun i => lag_mod_grid (Geometry.shiftedCurve q s) (D.atoms_grid i) n,
      hz, Curve.lag_zero, mul_zero, Finset.sum_const_zero]
  · simpa only [fun i => lag_mod_grid (Geometry.shiftedCurve q s) (D.atoms_grid i) n, hr]
      using D.tight r

theorem weighted_symbol_zero :
    ∑ i, (D.primal i : ℝ) * finiteSymbol q s D.lags D.dual (D.atoms i) = 0 := by
  simp only [finiteSymbol_actual, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  have he : (∑ i, (D.primal i : ℝ) * (D.dual n * (Geometry.shiftedCurve q s).lag n (D.atoms i))) =
      D.dual n * ∑ i, (D.primal i : ℝ) * (Geometry.shiftedCurve q s).lag n (D.atoms i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, D.lag_tight n hn, mul_zero]

theorem symbol_zero_support (i : Fin D.d) :
    finiteSymbol q s D.lags D.dual (D.atoms i) = 0 := by
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin D.d)),
      (D.primal j : ℝ) * finiteSymbol q s D.lags D.dual (D.atoms j) ≤ 0 :=
    fun j _ => mul_nonpos_of_nonneg_of_nonpos (D.primal j).coe_nonneg
      (D.symbol_nonpos _ (D.atoms j).property)
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp D.weighted_symbol_zero i (Finset.mem_univ _)
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast (D.primal_pos i).ne')

theorem symbol_slope_support (i : Fin D.d) :
    deriv (finiteSymbol q s D.lags D.dual) (D.atoms i : ℝ) = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards [Ioo_mem_nhds (D.atoms_grid i).1 (D.atoms_lt_pi i)] with x hx
  rw [D.symbol_zero_support]
  exact D.symbol_nonpos x ⟨hx.1.le, hx.2.le⟩

end RegularData
end polyak.ModeLocking
