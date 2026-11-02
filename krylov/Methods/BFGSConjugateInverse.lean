import krylov.Methods.BroydenEndpoints
import krylov.Methods.VirtualReference
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), actual conjugate BFGS inverse action.
Use: prove the genuine accumulated two-loop inverse model preserves every
real conjugate secant and inverts the true operator on the actual stored span.
Source: existing genuine BFGS endpoint/two-loop dictionary and the literal
observed update, with independently supplied actual nonzero energy domains. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual accumulated BFGS two-loop model satisfies every true stored
secant simultaneously on real pairwise conjugate observed pairs.
Use: full-cycle quasi-Newton inverse action is derived from the genuine
recursion, rather than postulated as a matrix model property.
Article: main_krylov, prop:classical(b).
Proof: the newest real secant cancels its backward component and is imposed
exactly. Both actual cross pairings with older secants vanish, so every genuine
older secant is preserved under the literal new two-loop update. -/
theorem inverseBFGSApply_conjugate_secants (c : ℝ) (W : List (E × E))
    (hdiag : ∀ p∈W,inner ℝ p.1 p.2≠0)
    (hconj : W.Pairwise (fun p q => inner ℝ p.1 q.2=0 ∧ inner ℝ p.2 q.1=0)) :
    ∀ p∈W,inverseBFGSApply c W p.2=p.1 := by
  induction W with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons p W ih =>
    have hc := List.pairwise_cons.mp hconj
    have hzero : inverseBFGSApply c W (0 : E)=0 := by
      rw [← inverseBroydenModel_bfgs,map_zero]
    have hhead : inverseBFGSApply c (p::W) p.2=p.1 := by
      rw [inverseBFGSApply]
      simp only [inv_mul_cancel₀ (hdiag p List.mem_cons_self),one_smul,sub_self,hzero,
        inner_zero_right,mul_zero,sub_zero,zero_add]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hhead
    · have hcross := hc.1 q hq
      rw [inverseBFGSApply]
      simp only [hcross.1,mul_zero,zero_smul,sub_zero,
        ih (fun p hp => hdiag p (List.mem_cons_of_mem _ hp)) hc.2 q hq,
        hcross.2,add_zero]

/-- On the actual stored physical span, the real accumulated conjugate BFGS
model is exactly the true inverse quadratic operator action.
Use: full-cycle inverse behavior follows without an assumed inverse matrix
or an extra condition on unobserved directions.
Article: main_krylov, prop:classical(b).
Proof: the genuine linear-map/two-loop dictionary gives a real linear model.
The proved true secant equations identify its composition with the actual
operator on every genuine stored generator, hence on their entire real span. -/
theorem inverseBFGSApply_conjugate_on_span (c : ℝ) (W : List (E × E))
    (Q : E →L[ℝ] E) (hy : ∀ p∈W,p.2=Q p.1)
    (hdiag : ∀ p∈W,inner ℝ p.1 p.2≠0)
    (hconj : W.Pairwise (fun p q => inner ℝ p.1 q.2=0 ∧ inner ℝ p.2 q.1=0))
    (v : E) (hv : v∈pairSpan W) : inverseBFGSApply c W (Q v)=v := by
  let H := inverseBroydenModel c (fun _ => 1) W
  have hsec := inverseBFGSApply_conjugate_secants c W hdiag hconj
  have h (w : E) (hw : w∈pairSpan W) : H (Q w)=w := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i,rfl⟩ := hw
      have hp := List.get_mem W i
      change H (Q (W.get i).1)=(W.get i).1
      rw [← hy (W.get i) hp]
      exact (inverseBroydenModel_bfgs c W _).trans (hsec _ hp)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add,map_add,hx,hy]
    | smul a x _ hx => rw [map_smul,map_smul,hx]
  exact (inverseBroydenModel_bfgs c W _).symm.trans (h v hv)

end
end krylov.Methods
