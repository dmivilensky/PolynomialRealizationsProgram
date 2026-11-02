import krylov.Methods.BroydenUpdate
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), genuine direct convex Broyden update.
Use: implement the original direct model formula and derive its real secant,
symmetry and positive-curvature domains for all native chronological updates.
Source: the direct Broyden formula printed in main_krylov, apE:broyden;
positivity follows by an exact completed quadratic form. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original observed direct Broyden correction vector with its true
old-model and observed secant curvature denominators.
Use: the direct quasi-Newton comparison uses the actual direct update.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenVector (B : E →ₗ[ℝ] E) (s y : E) : E :=
  (inner ℝ s y)⁻¹ • y-(inner ℝ s (B s))⁻¹ • B s

/-- The literal original direct Broyden model update from its observed pair.
Use: no inverse interpolation or postulated latest-information matrix is
substituted for the direct quasi-Newton recursion in the source comparison.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenUpdate (B : E →ₗ[ℝ] E) (s y : E) (phi : ℝ) : E →ₗ[ℝ] E :=
  let a := inner ℝ s (B s)
  let b := inner ℝ s y
  let v := directBroydenVector B s y
  B-a⁻¹ • ((innerSL ℝ s).toLinearMap.comp B).smulRight (B s)+
    b⁻¹ • (innerSL ℝ y).toLinearMap.smulRight y+
      (phi*a) • (innerSL ℝ v).toLinearMap.smulRight v

/-- The actual direct update has exactly its printed observed rank-update action.
Use: real scalar and vector perturbation calculations concern this genuine map.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: expand the actual linear rank-one maps and real observed coefficients. -/
theorem directBroydenUpdate_apply (B : E →ₗ[ℝ] E) (s y w : E) (phi : ℝ) :
    directBroydenUpdate B s y phi w=B w-
      (inner ℝ s (B w)/inner ℝ s (B s)) • B s+
      (inner ℝ y w/inner ℝ s y) • y+
      (phi*inner ℝ s (B s)*inner ℝ (directBroydenVector B s y) w) • directBroydenVector B s y := by
  simp only [directBroydenUpdate,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.smulRight_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,innerSL_apply_apply,
    smul_smul,div_eq_mul_inv]
  module

/-- The genuine direct Broyden correction vector is orthogonal to its
actual secant step whenever both real denominators are nonzero.
Use: the original interpolation term preserves the true new secant equation.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: both actual step pairings normalize to one and cancel exactly. -/
theorem directBroydenVector_pairing (B : E →ₗ[ℝ] E) (s y : E)
    (ha : inner ℝ s (B s)≠0) (hb : inner ℝ s y≠0) : inner ℝ (directBroydenVector B s y) s=0 := by
  rw [directBroydenVector,inner_sub_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_comm s y,real_inner_comm s (B s),inv_mul_cancel₀ hb,inv_mul_cancel₀ ha,sub_self]

/-- Every genuine direct Broyden update satisfies its actual new secant
on the real two nonzero observed/old-model curvature domains.
Use: the newest scalar model column is exact in the original comparison.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the actual correction vector annihilates the real step; the two
remaining native curvature quotients cancel the old action and impose y. -/
theorem directBroydenUpdate_secant (B : E →ₗ[ℝ] E) (s y : E) (phi : ℝ)
    (ha : inner ℝ s (B s)≠0) (hb : inner ℝ s y≠0) : directBroydenUpdate B s y phi s=y := by
  rw [directBroydenUpdate_apply,directBroydenVector_pairing B s y ha hb,div_self ha,
    real_inner_comm s y,div_self hb,one_smul,one_smul,sub_self,zero_add,mul_zero,zero_smul,add_zero]

/-- The actual direct Broyden update preserves genuine model symmetry.
Use: chronological native direct models retain their real self-adjoint forms.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: symmetry of the old actual action turns the subtractive term into a
symmetric rank-one form; the two remaining real rank-one forms are symmetric. -/
theorem directBroydenUpdate_symmetric (B : E →ₗ[ℝ] E) (hB : B.IsSymmetric)
    (s y : E) (phi : ℝ) : (directBroydenUpdate B s y phi).IsSymmetric := by
  intro u w
  rw [directBroydenUpdate_apply,directBroydenUpdate_apply]
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left,
    inner_add_right,inner_sub_right,real_inner_smul_right]
  have hu := hB s u
  have hw := hB s w
  change inner ℝ (B s) u=inner ℝ s (B u) at hu
  change inner ℝ (B s) w=inner ℝ s (B w) at hw
  rw [hB u w,← hu,← hw,real_inner_comm u (B s),real_inner_comm u y,
    real_inner_comm u (directBroydenVector B s y)]
  ring

/-- The genuine direct Broyden quadratic form is its exact completed old
positive form plus the two actual nonnegative secant/interpolation squares.
Use: positivity and later uniform denominator bounds are derived on the
literal direct update, without a supplied positive model field.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: expand the actual native rank-update action and the actual completed
vector; true old symmetry identifies the cross terms. Clear the two real
nonzero curvatures and verify the exact scalar completion identity. -/
theorem directBroydenUpdate_energy (B : E →ₗ[ℝ] E) (hB : B.IsSymmetric)
    (s y w : E) (phi : ℝ) (ha : inner ℝ s (B s)≠0) (hb : inner ℝ s y≠0) :
    let q := w-(inner ℝ s (B w)/inner ℝ s (B s)) • s
    inner ℝ w (directBroydenUpdate B s y phi w)=inner ℝ q (B q)+
      (inner ℝ y w)^2/inner ℝ s y+
        (phi*inner ℝ s (B s))*(inner ℝ (directBroydenVector B s y) w)^2 := by
  dsimp only
  rw [directBroydenUpdate_apply,map_sub,map_smul]
  simp only [inner_add_right,inner_sub_right,inner_sub_left,real_inner_smul_right,real_inner_smul_left]
  have he := hB s w
  change inner ℝ (B s) w=inner ℝ s (B w) at he
  rw [real_inner_comm (B s) w,he,real_inner_comm y w,real_inner_comm (directBroydenVector B s y) w]
  field_simp
  ring

/-- A genuine positive direct model, positive observed secant curvature and
nonnegative original interpolation give a genuinely positive next direct model.
Use: all original convex Broyden denominators are derived chronologically;
indeed the local positivity holds for every phi nonnegative.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: complete the old quadratic form. If its completed vector is nonzero,
the genuine old positivity is strict. If it vanishes, the nonzero test vector
is a nonzero multiple of the secant step and the actual positive observed
curvature makes the genuine secant square strict. -/
theorem directBroydenUpdate_positive (B : E →ₗ[ℝ] E) (hB : B.IsSymmetric)
    (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B w)) (s y : E)
    (hb : 0 < inner ℝ s y) (phi : ℝ) (hphi : 0≤phi) :
    ∀ w : E,w≠0 → 0 < inner ℝ w (directBroydenUpdate B s y phi w) := by
  have hs : s≠0 := by
    intro hz
    rw [hz,inner_zero_left] at hb
    exact lt_irrefl _ hb
  have ha := hpos s hs
  intro w hw
  let alpha := inner ℝ s (B w)/inner ℝ s (B s)
  let q := w-alpha • s
  have he := directBroydenUpdate_energy B hB s y w phi ha.ne' hb.ne'
  change inner ℝ w (directBroydenUpdate B s y phi w)=inner ℝ q (B q)+
    (inner ℝ y w)^2/inner ℝ s y+(phi*inner ℝ s (B s))*(inner ℝ (directBroydenVector B s y) w)^2 at he
  have hnonneg : 0≤(phi*inner ℝ s (B s))*(inner ℝ (directBroydenVector B s y) w)^2 :=
    mul_nonneg (mul_nonneg hphi ha.le) (sq_nonneg _)
  by_cases hq : q=0
  · have hwe : w=alpha • s := sub_eq_zero.mp hq
    have halpha : alpha≠0 := by intro hz;rw [hz,zero_smul] at hwe;exact hw hwe
    have hyw : inner ℝ y w≠0 := by
      rw [hwe,real_inner_smul_right,real_inner_comm s y]
      exact mul_ne_zero halpha hb.ne'
    have hstrict := div_pos (sq_pos_of_ne_zero hyw) hb
    rw [hq,inner_zero_left] at he
    linarith
  · have hstrict := hpos q hq
    have hsec := div_nonneg (sq_nonneg (inner ℝ y w)) hb.le
    linarith

end
end krylov.Methods
