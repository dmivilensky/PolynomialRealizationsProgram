import jacobi.GelfandLevitan.FiniteCompression

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the Sylvester identity and the elementary Woodbury inverse formula.
Use: the actual finite GL inverse gives the finite feature matrix inverse used to differentiate the original finite transformation kernel in The differential equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Swapping the two actual bounded feature maps preserves invertibility of identity plus their product, with its genuine explicit two-sided inverse.
Use: the actual finite GL inverse gives the finite feature matrix inverse used to differentiate the original finite transformation kernel in The differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the Sylvester identity; the inverse is I-A*(I+S*A)^(-1)*S.
Proof: use the independently given genuine inverse of I+S*A. In the left product the synthesis intertwines the two pencils; in the right product its true inverse equation cancels the same original feature terms. Both inverse identities are verified on arbitrary genuine inputs, so neither injectivity of the feature map nor finite dimension is needed. -/
theorem isUnit_id_add_swap_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : F →L[ℝ] E) (A : E →L[ℝ] F)
    (h : IsUnit (ContinuousLinearMap.id ℝ E+S ∘L A)) :
    IsUnit (ContinuousLinearMap.id ℝ F+A ∘L S) := by
  -- The explicit inverse acts on the same actual feature spaces; no spectrum or formal matrix variable replaces the given maps.
  let T := ContinuousLinearMap.id ℝ E+S ∘L A
  let Q := Ring.inverse T
  let B := ContinuousLinearMap.id ℝ F+A ∘L S
  let R := ContinuousLinearMap.id ℝ F-A ∘L Q ∘L S
  have hleft (x : E) : Q (T x)=x :=
    congrArg (fun U : E →L[ℝ] E => U x) (Ring.inverse_mul_cancel _ h)
  have hright (x : E) : T (Q x)=x :=
    congrArg (fun U : E →L[ℝ] E => U x) (Ring.mul_inverse_cancel _ h)
  refine ⟨⟨B,R,?_,?_⟩,rfl⟩
  · apply ContinuousLinearMap.ext
    intro y
    change y-A (Q (S y))+A (S (y-A (Q (S y))))=y
    rw [map_sub,map_sub]
    have he := congrArg A (hright (S y))
    change A (Q (S y)+S (A (Q (S y))))=A (S y) at he
    rw [map_add] at he
    rw [← he]
    abel
  · apply ContinuousLinearMap.ext
    intro y
    change y+A (S y)-A (Q (S (y+A (S y))))=y
    rw [map_add]
    have he := hleft (S y)
    change Q (S y+S (A (S y)))=S y at he
    rw [he]
    abel

end
end jacobi.GelfandLevitan
