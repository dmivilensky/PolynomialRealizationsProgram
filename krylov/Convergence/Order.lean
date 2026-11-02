import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, lem:rorder2, the definition preceding thm:Htransfer,
and Table s7-orders.
Use: state literal R-order bounds and convert eventual exponential barriers
into the article's global geometric-of-exponential estimate, including all
finite initial prefixes and stationary tails.
Source: Ortega and Rheinboldt (1970), elementary rescaling of errors.
-/
namespace krylov.Convergence
noncomputable section
open Filter Topology
open scoped BigOperators

/-- The article's literal R-order estimate, with a true geometric base
strictly between zero and one. No positivity of the errors is built in.
Article: main_krylov, s7:restart and lem:rorder2. -/
def HasROrder (e : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∃ C q : ℝ,0<C ∧ 0<q ∧ q<1 ∧ ∀ k : ℕ,e k≤C*q^(τ^k)

/-- Any eventual positive exponential barrier gives the literal global
R-order estimate. The finite initial prefix is absorbed into one constant.
Article: main_krylov, lem:rorder2, including zero errors. -/
theorem hasROrder_of_eventually_exp (e : ℕ → ℝ) (τ : ℝ)
    {C c : ℝ} (hC : 0<C) (hc : 0<c)
    (h : ∀ᶠ k in atTop,e k≤C*Real.exp (-c*τ^k)) : HasROrder e τ := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let P := ∑ j∈Finset.range N,|e j| *Real.exp (c*τ^j)
  have hP : 0≤P := Finset.sum_nonneg (fun _ _=>mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  refine ⟨C+P,Real.exp (-c),by positivity,Real.exp_pos _,Real.exp_lt_one_iff.mpr (by linarith),?_⟩
  intro k
  rw [←Real.exp_mul]
  by_cases hk : N≤k
  · exact (hN k hk).trans (mul_le_mul_of_nonneg_right (by linarith only [hP] : C≤C+P) (Real.exp_pos _).le)
  · have hp : |e k| *Real.exp (c*τ^k)≤P :=
      Finset.single_le_sum (fun j _=>mul_nonneg (abs_nonneg (e j)) (Real.exp_pos (c*τ^j)).le)
        (show k∈Finset.range N from Finset.mem_range.mpr (by omega))
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-c*τ^k)).le
    have he : (|e k| *Real.exp (c*τ^k))*Real.exp (-c*τ^k)=|e k| := by
      rw [show -c*τ^k= -(c*τ^k) by ring,Real.exp_neg]
      field_simp
    rw [he] at hh
    exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hC] : P≤C+P) (Real.exp_pos _).le))

/-- A shifted error tail with a positive exponential barrier has the same
literal R-order. Article: main_krylov, lem:rorder2. -/
theorem hasROrder_of_tail_exp (e : ℕ → ℝ) (τ : ℝ) (hτ : 0<τ)
    (N : ℕ) {C c : ℝ} (hC : 0<C) (hc : 0<c)
    (h : ∀ j : ℕ,e (N+j)≤C*Real.exp (-c*τ^j)) : HasROrder e τ := by
  apply hasROrder_of_eventually_exp e τ hC (div_pos hc (pow_pos hτ N))
  filter_upwards [eventually_ge_atTop N] with k hk
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  have he : -(c/τ^N)*τ^(N+j)= -c*τ^j := by
    rw [pow_add]
    field_simp
  rw [he]
  exact h j

/-- A smaller comparison sequence inherits an actual R-order bound.
Article: main_krylov, Table s7-orders, gradient/error comparisons. -/
theorem HasROrder.mono {e f : ℕ → ℝ} {τ : ℝ} (h : HasROrder e τ)
    {A : ℝ} (hA : 0<A) (hef : ∀ k,f k≤A*e k) : HasROrder f τ := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  refine ⟨A*C,q,mul_pos hA hC,hq,hq₁,?_⟩
  intro k
  exact (hef k).trans ((mul_le_mul_of_nonneg_left (hbound k) hA.le).trans_eq (mul_assoc _ _ _).symm)

/-- Eventual constant-factor comparisons preserve literal R-order; all
finite exceptions are absorbed into the actual global constant.
Article: main_krylov, Table s7-orders, intermediate query bounds. -/
theorem HasROrder.eventually_mono {e f : ℕ → ℝ} {τ : ℝ} (h : HasROrder e τ)
    {A : ℝ} (hA : 0<A) (hef : ∀ᶠ k in atTop,f k≤A*e k) : HasROrder f τ := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  have hc : 0< -Real.log q := neg_pos.mpr (Real.log_neg hq hq₁)
  apply hasROrder_of_eventually_exp f τ (mul_pos hA hC) hc
  filter_upwards [hef] with k hk
  have hh := (hk.trans (mul_le_mul_of_nonneg_left (hbound k) hA.le))
  rw [Real.rpow_def_of_pos hq] at hh
  simpa only [neg_neg,mul_assoc] using hh

/-- Every smaller positive order inherits the same actual error barrier.
Article: main_krylov, guaranteed R-orders in Table s7-orders. -/
theorem HasROrder.weaken {e : ℕ → ℝ} {τ σ : ℝ} (h : HasROrder e τ)
    (hσ : 0≤σ) (hστ : σ≤τ) : HasROrder e σ := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  refine ⟨C,q,hC,hq,hq₁,?_⟩
  intro k
  exact (hbound k).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq₁.le (pow_le_pow_left₀ hσ hστ k)) hC.le)

end
end krylov.Convergence
