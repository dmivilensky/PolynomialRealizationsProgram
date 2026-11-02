import jacobi.Support.CouplingBounds
import jacobi.Support.DiagonalBounds
import jacobi.Support.BoundaryDiagonal

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The complete printed coefficient lemma holds for the actual original
finite support matrix: one positive coupling lower bound, the true
initial diagonal bound, and the joint inverse-square perturbation bound
throughout the entire stated growing half-chain range.
Use: the true support Volterra kernel has uniformly positive original edge factors, and the original oscillatory wave recurrence is a summable inverse-square perturbation of the free one.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original support matrix satisfies every assertion of the printed coefficient lemma, with common constants and a genuine single degree threshold.
Use: the true support Volterra kernel has uniformly positive original edge factors, and the original oscillatory wave recurrence is a summable inverse-square perturbation of the free one.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: intersect the independently proved genuine coupling, interior diagonal and boundary estimates. For large enough original degree the full printed range consists of true interior edges; identify the exact original matrix coefficients and enlarge only the common positive upper constant. -/
theorem coefficient_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,
      |(naturalChain a b ha hb n).data.b 0|≤C ∧
      ∀m:ℕ,0<m→2*m≤n+6→
        c≤Real.sqrt ((naturalChain a b ha hb n).data.aSq m) ∧
        |Real.sqrt ((naturalChain a b ha hb n).data.aSq m)-1/2|+
          |(naturalChain a b ha hb n).data.b m|≤C/(m:ℝ)^2 := by
  -- Every estimate is for the actual original chain; the original finite tail is excluded by the proved common degree threshold.
  obtain ⟨c,hc,hlo⟩ := coupling_lower ha hb
  obtain ⟨A,hA,hAerr⟩ := coupling_error ha hb
  obtain ⟨B,hB,hBerr⟩ := diagonal_bounds ha hb
  obtain ⟨D,hD,hzero⟩ := diagonal_zero_bound ha hb
  refine ⟨c,A+B+D,hc,by positivity,?_⟩
  filter_upwards [hlo,hAerr,hBerr,hzero,eventually_ge_atTop (8:ℕ)] with n hn₀ hn₁ hn₂ hn₃ hlarge
  constructor
  · rw [naturalChain_diagonal a b ha hb (by omega : 0<n)]
    exact hn₃.trans (by linarith)
  · intro m hm hmn
    have hm' : m<n := by omega
    rw [naturalChain_sqrt_coupling a b ha hb hm hm',naturalChain_diagonal a b ha hb hm']
    refine ⟨hn₀ m hm hmn,?_⟩
    have h := add_le_add (hn₁ m hm hmn) (hn₂ m hm hmn)
    calc
      _ ≤ A/(m:ℝ)^2+B/(m:ℝ)^2 := h
      _ = (A+B)/(m:ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg (m:ℝ))

end
end jacobi.Support
