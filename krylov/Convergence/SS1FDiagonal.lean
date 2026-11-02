import krylov.Convergence.SplitAdmissibility
import krylov.Functions.TrapezoidSpectral

/-!
Article: main_krylov, thm:ss1F and condition (S).
Use: the improved diagonal estimate for the actual function-value model,
with the exact L3/12 oldest-segment term. The unbounded dimensionless split
coefficient is eliminated using the actual anchor remainder condition.
Source: the proved anchored Peano-kernel remainder, Banach38's proved
diagonal-to-mixed identity, and the exact midpoint/endpoint split identity.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions krylov.Tensor
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Under (S), the actual corrected observed diagonal differs from the
current genuine Hessian by the displacement to the newer endpoint, plus
the sharp quadratic segment and anchor remainders. -/
theorem ss1F_corrected_diagonal_bound
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → SymmetricCubic E) (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z∈S,HasFDerivAt f (D z) z)
    (hH : ∀ z∈S,HasFDerivAt D (H z) z)
    (hT : ∀ z∈S,HasFDerivAt H (T z).form z) (L : ℝ≥0)
    (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    (a s x : E) (ha : a∈S) (hb : a+s∈S) (hx : x∈S)
    (l C B : ℝ) (hB : 0≤B)
    (hbudget : ∀ h:E,‖h‖=1 → |(T (a+s)).form h h h|≤B)
    (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |correctedValueDiagonal f D a s l-H x s s|≤
      (B*C*‖x-(a+s)‖+(L:ℝ)*((1/12:ℝ)*‖s‖^2+
        (1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
        (1/2:ℝ)*‖x-(a+s)‖^2))*‖s‖^2 := by
  obtain ⟨R,hR,hbound⟩ := anchored_trapezoid_remainder_spectral
    f D H T S hS hD hH hT L hLip a s x ha hb hx l
  have hmix := cubic_diagonal_bound (T (a+s)) B hbudget (splitRemainder a s x l) s s
  have hsplit := split_half_deviation_bound a s x l C hw
  have hterm : |(T (a+s)).form (splitRemainder a s x l) s s|≤
      B*C*‖x-(a+s)‖*‖s‖^2 := by
    exact hmix.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hB) (norm_nonneg s))
        (norm_nonneg s)).trans_eq (by ring))
  have hrema : |R|≤(L:ℝ)*((1/12:ℝ)*‖s‖^2+
      (1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+(1/2:ℝ)*‖x-(a+s)‖^2)*‖s‖^2 := by
    apply hbound.trans
    have hh := mul_le_mul_of_nonneg_right hsplit (show 0≤‖s‖^3 by positivity)
    have hL := L.coe_nonneg
    nlinarith only [hh,hL,mul_nonneg hL (sub_nonneg.mpr hh)]
  change |(D (a+s)-D a) s-12*l*segmentValueDefect f D a s-H x s s|≤_
  change (D (a+s)-D a) s-12*l*segmentValueDefect f D a s-H x s s=
    -(T (a+s)).form (splitRemainder a s x l) s s+R at hR
  rw [hR]
  calc
    _ ≤ |-(T (a+s)).form (splitRemainder a s x l) s s|+|R| := abs_add_le _ _
    _ ≤ B*C*‖x-(a+s)‖*‖s‖^2+
        (L:ℝ)*((1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
          (1/2:ℝ)*‖x-(a+s)‖^2)*‖s‖^2 := by
      rw [abs_neg]
      exact add_le_add hterm hrema
    _ = _ := by ring

end
end krylov.Convergence
