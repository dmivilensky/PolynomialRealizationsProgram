import jacobi.Jacobi.SpectralLimit
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
An explicit product perturbation estimate makes the proved L1 spectral
convergence sufficient for convergence of the actual complex products.
Source: finite product telescoping, the exponential bound and completeness.
Use: controls the unchanged factors in the canonical-product perturbation estimate.
-/
namespace jacobi.Bessel
noncomputable section
open Filter
open scoped Topology

/-- A finite complex product is bounded by the exponential of the sum of its perturbation norms.
Use: controls the unchanged factors in the canonical-product perturbation estimate.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the triangle inequality and 1+x<=exp(x), formalized in mathlib.
Proof: bound the product norm by the product of factor norms, then use the community exponential product inequality. -/
theorem norm_finite_product_le (s : Finset ℕ) (u : ℕ → ℂ) :
    ‖∏ k∈s,(1+u k)‖ ≤ Real.exp (∑ k∈s,‖u k‖) := by
  apply (Finset.norm_prod_le s _).trans
  apply (Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) (fun k _ => ?_)).trans
    (Real.prod_one_add_le_exp_sum s (fun k => norm_nonneg (u k)))
  simpa only [norm_one] using norm_add_le (1:ℂ) (u k)

/-- A finite complex product is Lipschitz in the L1 distance between its perturbations, with an explicit exponential mass bound.
Use: passes the finite Jacobi product to the infinite actual Bessel product using full spectral L1 convergence.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the elementary telescoping proof of continuity of canonical products.
Proof: separate one factor, telescope the difference, and apply the triangle
and product inequalities. Each exponential coefficient is bounded by the
exponential of the combined perturbation masses. -/
theorem finite_product_lipschitz (s : Finset ℕ) (u v : ℕ → ℂ) :
    ‖(∏ k∈s,(1+u k))-(∏ k∈s,(1+v k))‖ ≤
      Real.exp (∑ k∈s,(‖u k‖+‖v k‖))*(∑ k∈s,‖u k-v k‖) := by
  classical
  -- This induction never divides by a factor, so the estimate includes actual spectral zeros.
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx,Finset.prod_insert hx,Finset.sum_insert hx,Finset.sum_insert hx]
    have hu : ‖1+u x‖ ≤ Real.exp ‖u x‖ :=
      (show ‖1+u x‖ ≤ 1+‖u x‖ by simpa only [norm_one] using norm_add_le (1:ℂ) (u x)).trans (by simpa [add_comm] using Real.add_one_le_exp ‖u x‖)
    have hp := norm_finite_product_le s v
    have he1 : Real.exp ‖u x‖*Real.exp (∑ k∈s,(‖u k‖+‖v k‖)) ≤
        Real.exp (‖u x‖+‖v x‖+∑ k∈s,(‖u k‖+‖v k‖)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [norm_nonneg (v x)]
    have he2 : Real.exp (∑ k∈s,‖v k‖) ≤
        Real.exp (‖u x‖+‖v x‖+∑ k∈s,(‖u k‖+‖v k‖)) := by
      apply Real.exp_le_exp.mpr
      have hs : (∑ k∈s,‖v k‖) ≤ ∑ k∈s,(‖u k‖+‖v k‖) :=
        Finset.sum_le_sum (fun k _ => le_add_of_nonneg_left (norm_nonneg (u k)))
      linarith [norm_nonneg (u x),norm_nonneg (v x)]
    rw [show (1+u x)*(∏ k∈s,(1+u k))-(1+v x)*(∏ k∈s,(1+v k))=
      (1+u x)*((∏ k∈s,(1+u k))-(∏ k∈s,(1+v k)))+(u x-v x)*(∏ k∈s,(1+v k)) by ring]
    calc
      _ ≤ ‖1+u x‖*‖(∏ k∈s,(1+u k))-(∏ k∈s,(1+v k))‖+‖u x-v x‖*‖∏ k∈s,(1+v k)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ Real.exp ‖u x‖*(Real.exp (∑ k∈s,(‖u k‖+‖v k‖))*(∑ k∈s,‖u k-v k‖))+
          ‖u x-v x‖*Real.exp (∑ k∈s,‖v k‖) :=
        add_le_add (mul_le_mul hu ih (norm_nonneg _) (Real.exp_nonneg _))
          (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right he1 (Finset.sum_nonneg (s := s) (fun k _ => norm_nonneg (u k-v k)))
        have h2 := mul_le_mul_of_nonneg_left he2 (norm_nonneg (u x-v x))
        nlinarith

/-- The infinite canonical product has the same explicit L1 perturbation estimate as its finite sections.
Use: transfers the true finite Jacobi products to the actual infinite Bessel product without assuming a product identity.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: absolute summability makes both products convergent. Pass the finite
estimate along natural prefixes; all partial norm sums are bounded by their
genuine total sums. -/
theorem infinite_product_lipschitz (u v : ℕ → ℂ)
    (hu : Summable (fun k => ‖u k‖)) (hv : Summable (fun k => ‖v k‖)) :
    ‖(∏' k,(1+u k))-(∏' k,(1+v k))‖ ≤
      Real.exp ((∑' k,‖u k‖)+(∑' k,‖v k‖))*(∑' k,‖u k-v k‖) := by
  -- All infinite sums and products used below have convergence proofs.
  have hd : Summable (fun k => ‖u k-v k‖) :=
    (hu.add hv).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_sub_le _ _)
  have ht := ((multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat.sub
    (multipliable_one_add_of_summable hv).hasProd.tendsto_prod_nat).norm
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  apply (finite_product_lipschitz (Finset.range n) u v).trans
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    rw [Finset.sum_add_distrib]
    exact add_le_add (hu.sum_le_tsum _ (fun k _ => norm_nonneg _))
      (hv.sum_le_tsum _ (fun k _ => norm_nonneg _))
  · exact hd.sum_le_tsum _ (fun k _ => norm_nonneg _)
  · exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  · exact Real.exp_nonneg _

end
end jacobi.Bessel
