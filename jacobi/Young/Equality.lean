import jacobi.Young.SechSquareODE
import jacobi.Young.Attainers
import jacobi.Variational.Congruence

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
Every nonzero measurable finite-energy equality density is, almost everywhere,
a positive multiple of a translated sech fourth power. Necessity follows
from Holder rigidity, the actual classical Green equation, its zero first
integral and proved global ODE uniqueness. The existing literal attainers
give sufficiency. This also proves the exact mass ratio used in elliptic strictness.
Source: the complete equality argument for the sharp Sobolev--Young inequality.
Use: excludes a Young equality minimizer in the strict elliptic regime.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- Necessity of the complete translated Young equality family.
Use: excludes a Young equality minimizer in the strict elliptic regime.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the actual equality potential obeys u''=4u-4c²u². Its finite H1
and cubic integrals give a zero first integral, fixing a positive maximum;
global ODE uniqueness gives u=(6/(4c²))sech²(x-x_0), and m=c²u². -/
theorem young_equality_necessary (m : Density) (hm : 0<m.mass)
    (he : 18*(observe m .second)^3=5*m.energy^4) :
    ∃ b x₀ : ℝ, 0<b ∧ m.value=ᵐ[volume] (fun x => b*sech (x-x₀)^4) := by
  -- Both the semilinear equation and all regularity are derived from the original measurable density.
  obtain ⟨c,hc,hae,hode⟩ := young_equality_classical m hm he
  have hp : ∃ x, 0<potential m x := by
    by_contra! hn
    have hz (x : ℝ) : potential m x=0 := le_antisymm (hn x) (potential_nonneg m x)
    have hh := (young_chain m).1
    simp_rw [hz] at hh
    simp only [zero_pow (by decide : 3≠0),integral_zero,mul_zero] at hh
    exact (not_le_of_gt (pow_pos (second_pos_of_mass_pos m hm) 3)) hh
  have ha : 0<4*c^2 := mul_pos (by norm_num) (sq_pos_of_pos hc)
  obtain ⟨x₀,hp',_⟩ := semilinear_classification ha (potential_hasDerivAt m) hode
    (potential_sobolev m).value_memLp.integrable_sq (potential_sobolev m).derivative_memLp.integrable_sq
    (potential_cube_integrable m) (potential_sobolev m).tendsto_zero.1
    (potential_sobolev m).tendsto_zero.2 hp
  refine ⟨c^2*(6/(4*c^2))^2,x₀,by positivity,?_⟩
  filter_upwards [hae] with x hx
  rw [hx,hp']
  dsimp only [sechSquareSolution]
  ring

/-- The full sharp Young equality classification for every nonzero density.
Use: supplies both necessity and sufficiency with precisely the article's printed sharp bound.
Article: jacobi, Theorem D.5.
Proof: cubing the printed equality gives the polynomial equality required by
the necessity theorem. Conversely null-set invariance transfers the already
verified translated literal attainer back to the original density. -/
theorem sharp_young_eq_iff (m : Density) (hm : 0<m.mass) :
    observe m .second=(5/18 : ℝ)^(1/3 : ℝ)*m.energy^(4/3 : ℝ) ↔
      ∃ b x₀ : ℝ, 0<b ∧ m.value=ᵐ[volume] (fun x => b*sech (x-x₀)^4) := by
  -- All powers are nonnegative, so the cube operation has no sign ambiguity.
  constructor
  · intro h
    apply young_equality_necessary m hm
    have hc : ((5/18 : ℝ)^(1/3 : ℝ))^3=5/18 := by
      simpa only [Nat.cast_one,pow_one] using third_power_cube (by norm_num : (0:ℝ)≤5/18) 1
    have hE : (m.energy^(4/3 : ℝ))^3=m.energy^4 := by
      simpa only [Nat.cast_ofNat] using third_power_cube m.energy_nonneg 4
    have hh := congrArg (fun r : ℝ => r^3) h
    rw [mul_pow,hc,hE] at hh
    linarith
  · rintro ⟨b,x₀,hb,hae⟩
    let q := (equalityFamily b hb.le).translate x₀
    have hmq : m.value=ᵐ[volume] q.value := hae
    rw [observe_congr hmq,Density.energy_congr hmq]
    exact translated_equalityFamily_sharp hb.le x₀

/-- Every nonzero Young equality density has the forced exact mass ratio two fifths.
Use: contradiction with the upper mass constraint proves strict elliptic improvement.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: classify the original density, transfer its actual mass and second
moment to the translated literal profile, and substitute their exact integrals. -/
theorem young_equality_mass_ratio (m : Density) (hm : 0<m.mass)
    (he : 18*(observe m .second)^3=5*m.energy^4) :
    observe m .second=(2/5 : ℝ)*m.mass^2 := by
  -- The full equality classification is necessary here; checking only explicit attainers would not suffice.
  obtain ⟨b,x₀,hb,hae⟩ := young_equality_necessary m hm he
  let q := (equalityFamily b hb.le).translate x₀
  have hmq : m.value=ᵐ[volume] q.value := hae
  rw [observe_congr hmq,Density.mass_congr hmq]
  rw [Density.translate_second,Density.translate_mass,equalityFamily_second,equalityFamily_mass]
  ring

end
end jacobi.Young
