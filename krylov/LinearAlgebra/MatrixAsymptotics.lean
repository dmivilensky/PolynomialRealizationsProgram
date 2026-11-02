import krylov.LinearAlgebra.CorrectionAsymptotics
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
Article: main_krylov, apA:lem:flagcd(d) and apG:mss, finite-matrix perturbation calculus.
Use: scalar coordinate calculations are transferred through the actual finite-dimensional
linear equivalence to the genuine spectral matrix norm, including rectangular matrices.
Source: continuity of finite-dimensional linear equivalences and mathlib's finite-product asymptotics.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Filter Asymptotics Topology
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {α : Type*} {n p q : ℕ} {f : Filter α}

/-- The actual finite matrix entries form a continuous linear coordinate equivalence.
Use: entrywise perturbation calculations retain the genuine spectral norm on their matrix side.
Article: main_krylov, apA:lem:flagcd(d), finite-coordinate calculus.
Source: every finite-dimensional linear equivalence and its inverse are continuous. -/
def matrixEntryEquiv (n p : ℕ) :
    Matrix (Fin n) (Fin p) ℝ ≃L[ℝ] ((Fin n × Fin p) → ℝ) :=
  ({ toFun := fun M ij => M ij.1 ij.2
     invFun := fun a i j => a (i, j)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
      Matrix (Fin n) (Fin p) ℝ ≃ₗ[ℝ] ((Fin n × Fin p) → ℝ)).toContinuousLinearEquiv

/-- Spectral matrix big-O is equivalent to big-O of every actual finite entry.
Use: compute first-order identities in coordinates without substituting an entrywise norm for the source norm.
Article: main_krylov, apA:lem:flagcd(d).
Proof: apply the actual continuous coordinate equivalence and its inverse,
then reuse the finite-product big-O characterization. -/
theorem matrix_bigO_iff_entry (M : α → Matrix (Fin n) (Fin p) ℝ) (s : α → ℝ) :
    M =O[f] s ↔ ∀ i j, (fun x => M x i j) =O[f] s := by
  let e := matrixEntryEquiv n p
  constructor
  · intro h i j
    have he := isBigO_pi.mp ((e.isBigO_comp M f).trans h)
    exact he (i, j)
  · intro h
    have he : (fun x => e (M x)) =O[f] s := isBigO_pi.mpr fun ij => h ij.1 ij.2
    exact (e.isBigO_comp_rev M f).trans he

/-- Spectral matrix little-o is equivalent to little-o of every actual finite entry.
Use: preserve the source's convergence and normalized remainder assertions under finite coordinate calculations.
Article: main_krylov, apG:mss.
Proof: the same genuine continuous coordinate equivalence transfers both directions
through the finite-product little-o theorem. -/
theorem matrix_littleO_iff_entry (M : α → Matrix (Fin n) (Fin p) ℝ) (s : α → ℝ) :
    M =o[f] s ↔ ∀ i j, (fun x => M x i j) =o[f] s := by
  let e := matrixEntryEquiv n p
  constructor
  · intro h i j
    have he := isLittleO_pi.mp ((e.isBigO_comp M f).trans_isLittleO h)
    exact he (i, j)
  · intro h
    have he : (fun x => e (M x)) =o[f] s := isLittleO_pi.mpr fun ij => h ij.1 ij.2
    exact (e.isBigO_comp_rev M f).trans_isLittleO he

/-- Actual rectangular matrix multiplication multiplies its two spectral asymptotic orders.
Use: first-order compressed increments may have arbitrary rectangular step windows.
Article: main_krylov, apA:lem:flagcd(d), matrix product calculus.
Proof: each actual product entry is a finite sum of products of its two actual input entries. -/
theorem matrix_mul_bigO (A : α → Matrix (Fin n) (Fin p) ℝ) (B : α → Matrix (Fin p) (Fin q) ℝ)
    (s t : α → ℝ) (hA : A =O[f] s) (hB : B =O[f] t) :
    (fun x => A x * B x) =O[f] (fun x => s x * t x) := by
  apply (matrix_bigO_iff_entry _ _).mpr
  intro i j
  have h : ∀ k ∈ (Finset.univ : Finset (Fin p)),
      (fun x => A x i k * B x k j) =O[f] (fun x => s x * t x) :=
    fun k _ => ((matrix_bigO_iff_entry A s).mp hA i k).mul ((matrix_bigO_iff_entry B t).mp hB k j)
  exact (Asymptotics.IsBigO.sum h).congr_left fun x => by simp only [Finset.sum_apply, Matrix.mul_apply]

/-- Transposition preserves every actual finite spectral matrix asymptotic order.
Use: the actual old-step congruence has a transposed step factor.
Article: main_krylov, apA:lem:flagcd(d).
Proof: transpose merely swaps actual finite entries in the proved coordinate criterion. -/
theorem matrix_transpose_bigO (A : α → Matrix (Fin n) (Fin p) ℝ) (s : α → ℝ)
    (hA : A =O[f] s) : (fun x => (A x)ᵀ) =O[f] s :=
  (matrix_bigO_iff_entry _ _).mpr fun i j => (matrix_bigO_iff_entry A s).mp hA j i

/-- Finite sums of actual spectral matrix bounds preserve their common order.
Use: assemble each finite flag sum from its genuine compressed increment remainders.
Article: main_krylov, apA:lem:flagcd(d), finite flag sums.
Proof: evaluate the finite sum of functions at the common perturbation parameter. -/
theorem matrix_sum_bigO (I : Finset ℕ) (A : ℕ → α → Matrix (Fin n) (Fin p) ℝ)
    (s : α → ℝ) (hA : ∀ k ∈ I, A k =O[f] s) :
    (fun x => ∑ k ∈ I, A k x) =O[f] s := by
  exact (Asymptotics.IsBigO.sum hA).congr_left fun x => by simp only [Finset.sum_apply]

/-- Constant rectangular left multiplication preserves every genuine spectral asymptotic order.
Use: fixed reference normalizers and flags do not change perturbation degree.
Article: main_krylov, apA:lem:flagcd(d), fixed-factor calculus.
Proof: apply rectangular product calculus with the bounded constant factor. -/
theorem matrix_const_mul_bigO (C : Matrix (Fin n) (Fin p) ℝ)
    (A : α → Matrix (Fin p) (Fin q) ℝ) (s : α → ℝ) (hA : A =O[f] s) :
    (fun x => C*A x) =O[f] s := by
  have hc : (fun _ : α => C) =O[f] (fun _ => (1 : ℝ)) := tendsto_const_nhds.isBigO_one ℝ
  simpa only [one_mul] using matrix_mul_bigO (fun _ => C) A (fun _ => 1) s hc hA

/-- Constant rectangular right multiplication preserves every genuine spectral asymptotic order.
Use: fixed reference normalizers and flags do not change perturbation degree.
Article: main_krylov, apA:lem:flagcd(d), fixed-factor calculus.
Proof: apply rectangular product calculus with the bounded constant factor. -/
theorem matrix_mul_const_bigO (A : α → Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin q) ℝ) (s : α → ℝ) (hA : A =O[f] s) :
    (fun x => A x*C) =O[f] s := by
  have hc : (fun _ : α => C) =O[f] (fun _ => (1 : ℝ)) := tendsto_const_nhds.isBigO_one ℝ
  simpa only [mul_one] using matrix_mul_bigO A (fun _ => C) s (fun _ => 1) hA hc

/-- Products of actual rectangular first-order perturbations have their actual reference product as limit.
Use: derive observed Gram errors from the perturbed operators and step matrices themselves.
Article: main_krylov, apA:lem:flagcd(d), actual observation expansion.
Proof: expand AB−A₀B₀=(A−A₀)B+A₀(B−B₀), with B bounded near its actual limit. -/
theorem matrix_product_first_order (A : α → Matrix (Fin n) (Fin p) ℝ)
    (B : α → Matrix (Fin p) (Fin q) ℝ)
    (A0 : Matrix (Fin n) (Fin p) ℝ) (B0 : Matrix (Fin p) (Fin q) ℝ) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hA : (fun x => A x-A0) =O[f] s)
    (hB : (fun x => B x-B0) =O[f] s) :
    (fun x => A x*B x-A0*B0) =O[f] s := by
  -- The actual varying right factor is bounded near its genuine reference value.
  have ht : Tendsto B f (𝓝 B0) := by
    simpa only [sub_add_cancel, zero_add] using (hB.trans_tendsto hs).add_const B0
  have hb := matrix_mul_bigO (fun x => A x-A0) B s (fun _ => 1) hA (ht.isBigO_one ℝ)
  have hb' : (fun x => (A x-A0)*B x) =O[f] s := by simpa only [mul_one] using hb
  have ha := matrix_const_mul_bigO A0 (fun x => B x-B0) s hB
  exact (hb'.add ha).congr_left fun x => by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel

/-- Replacing the two actual outer factors in a first-order rectangular product costs only quadratic order.
Use: derive the reference-step compressed increments from the actual perturbed step matrices.
Article: main_krylov, apA:lem:flagcd(d), X_l at the reference.
Proof: split the exact difference into (A−A₀)EB+A₀E(B−B₀); the actual B is bounded
near its limit and each remaining changed factor or increment has first order. -/
theorem matrix_triple_first_order {r : ℕ}
    (A : α → Matrix (Fin n) (Fin p) ℝ) (E : α → Matrix (Fin p) (Fin q) ℝ)
    (B : α → Matrix (Fin q) (Fin r) ℝ)
    (A0 : Matrix (Fin n) (Fin p) ℝ) (B0 : Matrix (Fin q) (Fin r) ℝ) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hA : (fun x => A x - A0) =O[f] s)
    (hE : E =O[f] s) (hB : (fun x => B x - B0) =O[f] s) :
    (fun x => A x * E x * B x - A0 * E x * B0) =O[f] (fun x => s x^2) := by
  have hbt : Tendsto B f (𝓝 B0) := by
    simpa only [sub_add_cancel, zero_add] using (hB.trans_tendsto hs).add_const B0
  have hb1 : B =O[f] (fun _ => (1 : ℝ)) := hbt.isBigO_one ℝ
  have ha1 : (fun _ : α => A0) =O[f] (fun _ => (1 : ℝ)) := tendsto_const_nhds.isBigO_one ℝ
  have hfirst := matrix_mul_bigO _ B _ _ (matrix_mul_bigO _ E s s hA hE) hb1
  have hsecond := matrix_mul_bigO _ (fun x => B x-B0) _ s
    (matrix_mul_bigO (fun _ => A0) E (fun _ => 1) s ha1 hE) hB
  have hf : (fun x => (A x-A0)*E x*B x) =O[f] (fun x => s x^2) := by
    simpa only [mul_one, ← pow_two] using hfirst
  have hg : (fun x => A0*E x*(B x-B0)) =O[f] (fun x => s x^2) := by
    simpa only [one_mul, ← pow_two] using hsecond
  -- The identity concerns the actual rectangular products, with no independence or inverse premise.
  have he : ∀ x, (A x-A0)*E x*B x+A0*E x*(B x-B0) = A x*E x*B x-A0*E x*B0 := by
    intro x
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  simpa only [he] using hf.add hg

/-- Actual old-step congruences have the printed quadratic replacement error at their reference steps.
Use: the actual first-order flag sums may be evaluated at the fixed nondegenerate reference window.
Article: main_krylov, apA:lem:flagcd(d), compressed increment expansion.
Proof: transpose preserves the actual spectral first-order step error; apply the
proved rectangular triple-product expansion to SᵀES. -/
theorem matrix_congruence_first_order (S : α → Matrix (Fin n) (Fin p) ℝ)
    (E : α → Matrix (Fin n) (Fin n) ℝ) (S0 : Matrix (Fin n) (Fin p) ℝ) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hS : (fun x => S x-S0) =O[f] s) (hE : E =O[f] s) :
    (fun x => (S x)ᵀ*E x*S x-S0ᵀ*E x*S0) =O[f] (fun x => s x^2) := by
  have ht := matrix_transpose_bigO (fun x => S x-S0) s hS
  simp only [transpose_sub] at ht
  exact matrix_triple_first_order (fun x => (S x)ᵀ) E S S0ᵀ S0 s hs ht hE hS

end
end krylov.LinearAlgebra
