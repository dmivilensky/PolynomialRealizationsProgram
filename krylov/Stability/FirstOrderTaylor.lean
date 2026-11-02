import krylov.Stability.CompactSmooth
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch and thm:I, true C2 first-order vector remainder.
Use: reuse the actual compact Taylor theorem to turn proved semantic output
jets into genuine quadratic error bounds without assuming a remainder.
Source: the proved real compact integral Taylor estimate and actual first
Frechet/ordinary derivative identification, specialized at the original reference.
-/

namespace krylov.Stability
noncomputable section
open Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every actual C2 real-parameter vector output has a genuine quadratic
remainder around its proved first derivative.
Use: actual launch, XRFC and cancellation outputs share this real Taylor step.
Article: main_krylov, prop:launch; thm:I; lem:U.
Proof: the existing compact smooth Taylor theorem gives an actual radius and
constant at the singleton reference. Expand its true degree-one Taylor
polynomial and identify its actual derivative with the supplied proved first jet. -/
theorem c2_first_order_remainder (f : ℝ → F) (v : F)
    (hf : ContDiffAt ℝ 2 f 0) (hv : HasDerivAt f v 0) :
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖f t-f 0-t • v‖≤C*t^2 := by
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_smooth_taylor f 2 ({0} : Set ℝ) isCompact_singleton
    (by intro x hx;rw [Set.mem_singleton_iff.mp hx];exact hf)
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht
  have h := hbound 0 (Set.mem_singleton 0) t (by simpa only [Real.norm_eq_abs] using ht) 2 (by decide) le_rfl
  have hT : taylorPolynomial f 2 0 t=f 0+t • v := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,zero_add]
    rw [fderiv_eq_smul_deriv,hv.deriv]
  rw [hT] at h
  simpa only [zero_add,sub_add_eq_sub_sub,Real.norm_eq_abs,sq_abs] using h

end
end krylov.Stability
