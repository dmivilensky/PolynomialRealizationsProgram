import nesterov.Rates.Quadratic
import Mathlib.Analysis.Subadditive

/-!
Article: Definition `def:rate`, Lemma `lem:envelope` and Appendix A.
Use: Fekete's lemma proves the actual all-Hilbert uniform root limit and its
positive-horizon infimum, without stability assumptions. The positive lower
base is supplied by genuine endpoint quadratic trajectories.
-/
namespace nesterov.Rates
noncomputable section
open Set Filter
open scoped Topology
variable (M : StationaryMethod)

/-- The infimum of the logarithmic uniform envelope per positive horizon. -/
def exponent (μ L : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (envelope M μ L n) / n) '' Ici 1)

/-- The genuine uniform worst-case distance rate. -/
def rate (μ L : ℝ) : ℝ := Real.exp (exponent M μ L)

theorem log_envelope_subadditive {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Subadditive (fun n => Real.log (envelope M μ L n)) := by
  intro m n
  calc
    _ ≤ Real.log (envelope M μ L m * envelope M μ L n) :=
      Real.log_le_log (envelope_pos M hμ hμL _) (envelope_submultiplicative M μ L m n)
    _ = _ := Real.log_mul (ne_of_gt (envelope_pos M hμ hμL _))
      (ne_of_gt (envelope_pos M hμ hμL _))

theorem log_envelope_bddBelow {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    BddBelow (range (fun n : ℕ => Real.log (envelope M μ L n)/n)) := by
  obtain ⟨b,hb,hbound⟩ := envelope_lower_base M hμ hμL
  refine ⟨min (Real.log b) 0, ?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n=0
  · simp [hn]
  · have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh := Real.log_le_log (pow_pos hb n) (hbound n)
    rw [Real.log_pow] at hh
    exact (min_le_left _ _).trans ((le_div_iff₀ hnpos).mpr (by nlinarith))

theorem tendsto_log_envelope_div {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Tendsto (fun n : ℕ => Real.log (envelope M μ L n)/n) atTop (𝓝 (exponent M μ L)) := by
  simpa only [Subadditive.lim,exponent] using
    (log_envelope_subadditive M hμ hμL).tendsto_lim (log_envelope_bddBelow M hμ hμL)

theorem rate_pos (μ L : ℝ) : 0<rate M μ L := Real.exp_pos _

theorem tendsto_envelope_root {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Tendsto (fun n : ℕ => envelope M μ L n ^ ((n:ℝ)⁻¹)) atTop (𝓝 (rate M μ L)) := by
  have hh := (Real.continuous_exp.tendsto _).comp (tendsto_log_envelope_div M hμ hμL)
  simpa only [Function.comp_def,rate,Real.rpow_def_of_pos (envelope_pos M hμ hμL _),
    div_eq_mul_inv] using hh

theorem exponent_le_div {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) {n : ℕ} (hn : n≠0) :
    exponent M μ L ≤ Real.log (envelope M μ L n)/n := by
  simpa only [Subadditive.lim,exponent] using
    (log_envelope_subadditive M hμ hμL).lim_le_div (log_envelope_bddBelow M hμ hμL) hn

theorem rate_isGLB {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    IsGLB ((fun n : ℕ => envelope M μ L n ^ ((n:ℝ)⁻¹)) '' Ici 1) (rate M μ L) := by
  constructor
  · rintro _ ⟨n,hn,rfl⟩
    change 1≤n at hn
    change rate M μ L ≤ envelope M μ L n ^ ((n:ℝ)⁻¹)
    rw [rate,Real.rpow_def_of_pos (envelope_pos M hμ hμL n)]
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv] using exponent_le_div M hμ hμL (by omega : n≠0)
  · intro b hb
    apply ge_of_tendsto (tendsto_envelope_root M hμ hμL)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hb ⟨n,hn,rfl⟩

theorem rate_eq_inf {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    rate M μ L = sInf ((fun n : ℕ => envelope M μ L n ^ ((n:ℝ)⁻¹)) '' Ici 1) :=
  ((rate_isGLB M hμ hμL).csInf_eq ⟨_,1,by simp,rfl⟩).symm

theorem rate_pow_le_envelope {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) (n : ℕ) :
    rate M μ L ^ n ≤ envelope M μ L n := by
  by_cases hn : n=0
  · simp [hn,envelope_zero M hμ hμL]
  · have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh := (le_div_iff₀ hnpos).mp (exponent_le_div M hμ hμL hn)
    rw [rate,← Real.exp_nat_mul,← Real.exp_log (envelope_pos M hμ hμL n)]
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem le_rate_of_pow_le {μ L b : ℝ} (hμ : 0<μ) (hμL : μ<L) (hb : 0≤b)
    (h : ∀ n : ℕ,b^n≤envelope M μ L n) : b≤rate M μ L := by
  apply ge_of_tendsto (tendsto_envelope_root M hμ hμL)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := Real.rpow_le_rpow (pow_nonneg hb n) (h n) (by positivity : 0≤(n:ℝ)⁻¹)
  simpa only [Real.pow_rpow_inv_natCast hb (by omega : n≠0)] using hh

/-- Every original scalar quadratic eigenvalue bounds the full nonlinear rate. -/
theorem characteristicRoot_norm_le_rate {μ L lam : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hlam : lam∈Set.Icc μ L) {z : ℂ} (hz : M.characteristic lam z=0) : ‖z‖≤rate M μ L :=
  le_rate_of_pow_le M hμ hμL (norm_nonneg z)
    (characteristicRoot_pow_le_envelope M hμ hμL hlam z hz)

/-- A strict rate upper bound is equivalent to one uniform geometric bound,
with a slightly larger factor when necessary. -/
theorem exists_envelope_le_mul_pow {μ L R : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hR : rate M μ L<R) : ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope M μ L n≤C*R^n := by
  have hRp : 0<R := (rate_pos M μ L).trans hR
  have he : exponent M μ L<Real.log R := by
    rw [← Real.exp_lt_exp,Real.exp_log hRp]
    exact hR
  have hevent : ∀ᶠ n : ℕ in atTop,envelope M μ L n≤R^n := by
    filter_upwards [(tendsto_log_envelope_div M hμ hμL).eventually (gt_mem_nhds he),
      eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    have hh := (div_lt_iff₀ hnpos).mp hn
    rw [← Real.exp_log (envelope_pos M hμ hμL n),← Real.rpow_natCast,Real.rpow_def_of_pos hRp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  let C : ℝ := 1+∑ k ∈ Finset.range N,envelope M μ L k/R^k
  have hC : 1≤C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ =>
      div_nonneg (envelope_nonneg M μ L k) (pow_pos hRp k).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N≤n
  · exact (hN n hn).trans (by nlinarith [pow_pos hRp n])
  · have hs : envelope M μ L n/R^n≤∑ k ∈ Finset.range N,envelope M μ L k/R^k :=
      Finset.single_le_sum (fun k _ => div_nonneg (envelope_nonneg M μ L k)
        (pow_pos hRp k).le) (Finset.mem_range.mpr (by omega))
    apply (div_le_iff₀ (pow_pos hRp n)).mp
    dsimp [C]
    linarith

end
end nesterov.Rates
