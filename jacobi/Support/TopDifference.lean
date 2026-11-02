import jacobi.Support.TopRatioError
import jacobi.Support.TopValueBounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine original top-node solution has the complete printed first-
difference estimate, including every small mesh index on the original
growing range. Its actual positive normalization is preserved.
Use: the original Volterra first-difference estimate supplies the oscillatory envelope's actual transition-state derivative bound, and the kernel limit uses the same original solution.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The genuine original support top-node solution satisfies the complete uniform first-difference power bound.
Use: the original Volterra first-difference estimate supplies the oscillatory envelope's actual transition-state derivative bound, and the kernel limit uses the same original solution.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the actual adjacent positive top-node squares have precisely the original birth/death ratio. Its proved first-order index error controls the genuine positive value difference, and the actual top-node upper power bound gives the stated exponent. -/
theorem topValue_difference {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→
      |topValue a b ha hb n (m+1)-topValue a b ha hb n m|≤C*((m:ℝ)+1)^(gamma a-1) := by
  -- The signed original value difference is controlled using the actual positive square-root branch at both adjacent degrees.
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_bounds ha hb
  obtain ⟨D,hD,herr⟩ := topRatio_error ha hb
  refine ⟨C*D,mul_pos hC hD,?_⟩
  filter_upwards [hbound,herr,eventually_ge_atTop (8:ℕ)] with n hn he hlarge
  intro m hm
  have hm' : m<n := by omega
  have hu : 0<topValue a b ha hb n m := naturalPolynomial_top_pos ha hb (by omega)
  have hv : 0≤topValue a b ha hb n (m+1) := (naturalPolynomial_top_pos ha hb (by omega)).le
  have hrec : topValue a b ha hb n (m+1)^2=topValue a b ha hb n m^2*
      (coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)) :=
    naturalPolynomial_top_square_succ ha hb hm'
  have h := positive_square_difference hu hv hrec
  have hx : 0<(m:ℝ)+1 := by positivity
  calc
    _ ≤ topValue a b ha hb n m*|coefficientA a b (n+1) m/coefficientC a b (n+1) (m+1)-1| := h
    _ ≤ (C*((m:ℝ)+1)^gamma a)*(D/((m:ℝ)+1)) :=
      mul_le_mul (hn m hm).2 (he m hm) (abs_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_sub_one hx.ne']; ring

end
end jacobi.Support
