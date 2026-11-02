import jacobi.Jacobi.RegularPotential

/-!
Article: jacobi, Proposition B.1.
The true derivative of the actual smooth primitive is the regular
potential also at zero. A uniform derivative bound therefore gives the
literal Lipschitz bound and the source linear estimate |R(t)|<=C*t.
Use: bounds and differentiates the exact phase correction, rather than an unrelated integral primitive.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual regular primitive has its genuine smooth derivative throughout the closed comparison interval, including zero.
Use: bounds and differentiates the exact phase correction, rather than an unrelated integral primitive.
Article: jacobi, Proposition B.1.
Proof: its proved analytic extension supplies the true ordinary derivative, whose definition is precisely the original regular potential. -/
theorem regularPrimitive_derivative (a b : ℝ) {t : ℝ} (ht : t∈Icc 0 (3*Real.pi/4)) :
    HasDerivAt (regularPrimitive a b) (regularPotential a b t) t :=
  (regularPrimitive_analytic a b ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,Real.pi_pos]⟩).differentiableAt.hasDerivAt

/-- A genuine uniform potential bound gives the full Lipschitz bound for the literal source primitive on the complete comparison interval.
Use: replaces the primitive at the actual finite angle by its value at the explicit model angle in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: apply the community mean-value theorem on the original compact
convex comparison interval to the actual primitive derivative. -/
theorem regularPrimitive_lipschitz (a b C : ℝ)
    (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {s t : ℝ} (hs : s∈Icc 0 (3*Real.pi/4)) (ht : t∈Icc 0 (3*Real.pi/4)) :
    |regularPrimitive a b t-regularPrimitive a b s|≤C*|t-s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (regularPrimitive_derivative a b hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
    (convex_Icc 0 (3*Real.pi/4)) hs ht
  simpa only [Real.norm_eq_abs] using h

/-- The actual primitive has the original uniform linear endpoint bound, with its integration constant proved to vanish.
Use: controls both genuine initial and terminal finite phase corrections in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: specialize the actual Lipschitz estimate to zero and use the proved original value R(0)=0. -/
theorem regularPrimitive_linear (a b C : ℝ)
    (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {t : ℝ} (ht : t∈Icc 0 (3*Real.pi/4)) : |regularPrimitive a b t|≤C*t := by
  have h := regularPrimitive_lipschitz a b C hbound ⟨le_rfl,by positivity⟩ ht
  simpa only [regularPrimitive_zero,sub_zero,abs_of_nonneg ht.1] using h

end
end jacobi.Jacobi
