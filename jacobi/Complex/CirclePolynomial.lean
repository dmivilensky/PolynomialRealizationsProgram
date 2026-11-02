import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Article: jacobi, Proposition C.2.
Polynomial bounds on any sequence of expanding circles make an entire
function a polynomial. If it has no zeros, the polynomial is constant.
For the actual characteristic quotient this replaces a general
Hadamard factorization theorem by Cauchy estimates, the community
entire Taylor expansion, and the fundamental theorem of algebra.
Use: circle_power_bound_polynomial truncates the actual entire Taylor expansion of the characteristic quotient.
-/
namespace jacobi.Complex
noncomputable section
open Set Filter Metric _root_.Complex
open scoped Topology

/-- Polynomial growth on expanding circles forces every higher genuine Taylor derivative at their common center to vanish.
Use: circle_power_bound_polynomial truncates the actual entire Taylor expansion of the characteristic quotient.
Article: jacobi, Proposition C.2.
Source: Cauchy's derivative estimates, mathlib Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le.
Proof: the n-th derivative is bounded by n!*C/R^(n-N) on the expanding circles. For n>N that bound tends to zero, so its fixed nonnegative norm is zero. -/
theorem circle_power_bound_derivative_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (C : ℝ) (N : ℕ)
    (hb : ∀ᶠ m:ℕ in atTop,∀ z∈sphere c (R m),‖f z‖≤C*(R m)^N)
    {n : ℕ} (hn : N<n) : iteratedDeriv n f c=0 := by
  -- No lower or upper spacing condition is imposed on the radii; only their actual divergence is used.
  have hl := ((tendsto_pow_atTop (Nat.sub_pos_of_lt hn).ne').comp hR).const_div_atTop ((n.factorial:ℝ)*C)
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply ge_of_tendsto hl
  filter_upwards [hb,hR.eventually (eventually_gt_atTop (0:ℝ))] with m hm hr
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf.diffContOnCl hm
  apply h.trans_eq
  have hp : (R m)^n=(R m)^N*(R m)^(n-N) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  dsimp only [Function.comp_apply]
  field_simp [(pow_pos hr N).ne',(pow_pos hr (n-N)).ne']

/-- An entire function bounded by one polynomial power on expanding circles is an actual complex polynomial in the shifted energy variable.
Use: circle_power_bound_zero_free_constant proves constancy of the genuine original characteristic quotient without assuming Hadamard factorization.
Article: jacobi, Proposition C.2.
Source: Cauchy estimates and the entire Taylor expansion, mathlib Complex.taylorSeries_eq_of_entire'.
Proof: all actual Taylor derivatives beyond the bound degree vanish by the proved Cauchy estimate. The community global entire Taylor series therefore equals its finite original Taylor polynomial everywhere. -/
theorem circle_power_bound_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (C : ℝ) (N : ℕ)
    (hb : ∀ᶠ m:ℕ in atTop,∀ z∈sphere c (R m),‖f z‖≤C*(R m)^N) :
    ∃ P:Polynomial ℂ,∀ z,f z=P.eval (z-c) := by
  -- The polynomial coefficients are the genuine derivatives of the original entire function, not chosen spectral interpolation data.
  let P : Polynomial ℂ := ∑ n∈Finset.range (N+1),
    Polynomial.monomial n ((n.factorial:ℂ)⁻¹*iteratedDeriv n f c)
  refine ⟨P,fun z => ?_⟩
  rw [← taylorSeries_eq_of_entire' c z hf]
  rw [tsum_eq_sum (s := Finset.range (N+1)) (fun n hn => by
    have hd := circle_power_bound_derivative_zero hf c hR C N hb
      (show N<n by have h : ¬n<N+1 := fun h => hn (Finset.mem_range.mpr h); omega)
    rw [hd,mul_zero,zero_mul])]
  simp only [P,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

/-- A zero-free entire function with polynomial growth on expanding circles is constant.
Use: the original midpoint separated-product quotient has its constant factor determined by the proved contour bounds and the actual negative-energy normalization.
Article: jacobi, Proposition C.2.
Source: Cauchy derivative estimates, the entire Taylor expansion, and the fundamental theorem of algebra.
Proof: the actual entire function is a polynomial by the preceding theorem. A positive-degree complex polynomial would have a root, contradicting the proved zero-free property. Hence it is constant, with its genuine value at the original center. -/
theorem circle_power_bound_zero_free_constant {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hz : ∀ z,f z≠0) (c : ℂ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (C : ℝ) (N : ℕ)
    (hb : ∀ᶠ m:ℕ in atTop,∀ z∈sphere c (R m),‖f z‖≤C*(R m)^N) :
    ∀ z,f z=f c := by
  -- Constancy follows from actual global complex polynomial uniqueness, not just equality of two characteristic zero sets.
  obtain ⟨P,hP⟩ := circle_power_bound_polynomial hf c hR C N hb
  have hdeg : P.degree≤0 := by
    by_contra h
    obtain ⟨z,hz'⟩ := _root_.Complex.exists_root (lt_of_not_ge h)
    exact hz (z+c) (by rw [hP,add_sub_cancel_right]; exact hz')
  intro z
  rw [hP,hP,Polynomial.eq_C_of_degree_le_zero hdeg,Polynomial.eval_C,Polynomial.eval_C]

end
end jacobi.Complex
