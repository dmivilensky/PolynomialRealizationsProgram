import jacobi.Finite.PrefixGronwall
import Mathlib.Analysis.Complex.Norm

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
A bounded nested triangular Volterra equation is stable under a
uniform residual. The estimate is valid at arbitrary complex energy
on the actual finite prefix, with no small-energy assumption.
Source: finite-prefix discrete Gronwall inequality.
Use: the complex support edge proof applies this estimate to the actual normalized wave minus the actual reference core; the preceding mesh limit supplies a vanishing residual and bounded scaled energy supplies a uniform exponential.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- A genuine bounded complex nested finite Volterra equation amplifies its uniform residual by at most the explicit Gronwall exponential.
Use: the complex support edge proof applies this estimate to the actual normalized wave minus the actual reference core; the preceding mesh limit supplies a vanishing residual and bounded scaled energy supplies a uniform exponential.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: prefix_gronwall, the already proved finite-prefix discrete Gronwall inequality.
Proof: estimate both actual finite sums in norm. Each inner row is bounded by the full preceding norm sum, and there are exactly m such rows. On the original prefix replace m by M, apply discrete Gronwall and simplify its exact exponent. -/
theorem nested_volterra_stability (e:ℕ→ℂ) (K:ℕ→ℕ→ℂ) (d:ℂ) (M:ℕ)
    {B ε:ℝ} (hB:0≤B) (hε:0≤ε)
    (hK:∀l<M,∀j≤l,‖K l j‖≤B)
    (hr:∀m≤M,‖e m-d*∑l∈range m,∑j∈range (l+1),K l j*e j‖≤ε) :
    ‖e M‖≤ε*exp (‖d‖*B*(M:ℝ)^2) := by
  -- Only the same original finite prefix is involved in the residual and stability estimates.
  have htri : ∀m≤M,‖e m‖≤ε+(‖d‖*B*(M:ℝ))*∑j∈range m,‖e j‖ := by
    intro m hm
    have hsum : ‖∑l∈range m,∑j∈range (l+1),K l j*e j‖≤
        B*(m:ℝ)*∑j∈range m,‖e j‖ := by
      calc
        _ ≤ ∑l∈range m,∑j∈range (l+1),‖K l j*e j‖ :=
          (norm_sum_le _ _).trans (sum_le_sum (fun l _ => norm_sum_le _ _))
        _ ≤ ∑_l∈range m,B*∑j∈range m,‖e j‖ := by
          apply sum_le_sum
          intro l hl
          have hlm := mem_range.mp hl
          calc
            _ ≤ ∑j∈range (l+1),B*‖e j‖ := by
              apply sum_le_sum
              intro j hj
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hK l (by omega) j (by have := mem_range.mp hj; omega))
                (norm_nonneg _)
            _ = B*∑j∈range (l+1),‖e j‖ := (mul_sum _ _ _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun j _ _ => norm_nonneg (e j))) hB
        _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring
    have heq : e m=(e m-d*∑l∈range m,∑j∈range (l+1),K l j*e j)+
        d*∑l∈range m,∑j∈range (l+1),K l j*e j := by ring
    calc
      ‖e m‖ ≤ ε+‖d‖*‖∑l∈range m,∑j∈range (l+1),K l j*e j‖ := by
        nth_rw 1 [heq]
        exact (norm_add_le _ _).trans (by rw [norm_mul]; exact add_le_add (hr m hm) le_rfl)
      _ ≤ ε+‖d‖*(B*(m:ℝ)*∑j∈range m,‖e j‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
      _ ≤ ε+‖d‖*(B*(M:ℝ)*∑j∈range m,‖e j‖) := by
        gcongr
      _ = _ := by ring
  have h := prefix_gronwall hε (by positivity : 0≤‖d‖*B*(M:ℝ)) M htri
  convert h using 1
  congr 2
  ring

end
end jacobi.Finite
