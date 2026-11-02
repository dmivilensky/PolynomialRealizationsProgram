import jacobi.Variational.EnergyVariation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
The cube of the positive part is continuously differentiable even at the
free boundary. Its genuine pointwise derivative supplies the potential
term in the conserved energy of the actual elliptic optimizer equation.
Source: elementary one-variable differential calculus and the difference-quotient criterion.
Use: differentiates the conserved energy of the actual clipped elliptic ODE at every point.
-/
namespace jacobi.Variational
noncomputable section
open Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Cubing the positive part removes its derivative corner at the free boundary.
Use: differentiates the conserved energy of the actual clipped elliptic ODE at every point.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: away from zero the function is either the ordinary cube or zero.
At zero its difference quotient lies between zero and x², which tends to zero. -/
theorem positiveCube_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max y 0)^3) (3*(max x 0)^2) x := by
  -- The boundary point is proved directly, not omitted as an a.e. exceptional set.
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hn : ∀ᶠ y : ℝ in 𝓝 x,y<0 := Iio_mem_nhds hx
    have he : (fun y : ℝ => (max y 0)^3)=ᶠ[𝓝 x] fun _ => (0:ℝ) :=
      hn.mono fun y hy => by
        change (max y 0)^3=0
        rw [max_eq_right hy.le,zero_pow (by decide : 3≠0)]
    simpa only [max_eq_right hx.le,zero_pow (by decide : 2≠0),mul_zero] using
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  · subst x
    have hbounds (t : ℝ) : 0≤t⁻¹*(max t 0)^3 ∧ t⁻¹*(max t 0)^3≤t^2 := by
      by_cases ht : t≤0
      · simp only [max_eq_right ht,zero_pow (by decide : 3≠0),mul_zero,le_refl,true_and]
        exact sq_nonneg t
      · have ht0 : 0<t := lt_of_not_ge ht
        rw [max_eq_left ht0.le]
        have he : t⁻¹*t^3=t^2 := by field_simp
        rw [he]
        exact ⟨sq_nonneg t,le_rfl⟩
    have ht : Tendsto (fun t : ℝ => t^2) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2≠0)] using
        ((continuous_pow 2).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have h := squeeze_zero (fun t => (hbounds t).1) (fun t => (hbounds t).2) ht
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [zero_add,max_self,zero_pow (by decide : 3≠0),
      zero_pow (by decide : 2≠0),mul_zero,sub_zero,smul_eq_mul] using h
  · have hn : ∀ᶠ y : ℝ in 𝓝 x,0<y := Ioi_mem_nhds hx
    have he : (fun y : ℝ => (max y 0)^3)=ᶠ[𝓝 x] fun y => y^3 :=
      hn.mono fun y hy => by change (max y 0)^3=y^3; rw [max_eq_left hy.le]
    simpa [max_eq_left hx.le] using
      ((hasDerivAt_id x).pow 3).congr_of_eventuallyEq he

end
end jacobi.Variational
