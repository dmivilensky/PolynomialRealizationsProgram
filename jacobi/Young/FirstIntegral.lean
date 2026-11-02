import jacobi.Young.SemilinearUniqueness
import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The polynomial first integral is constant by the classical differential
equation. Finite Sobolev and cubic integrals force this constant to be zero
on the infinite line. Thus the maximum height is fixed without unproved
endpoint limits for the derivative.
Source: conservation of the autonomous one-dimensional ODE energy.
Use: fixes the maximum of a Young equality potential and the free-mass elliptic profile.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A finite-energy classical semilinear Green solution has its exact zero first integral.
Use: fixes the maximum of a Young equality potential and the free-mass elliptic profile.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: differentiate the polynomial conserved energy. It is constant on the
line, and integrability of all three terms excludes a nonzero constant. -/
theorem semilinear_first_integral {f d : ℝ → ℝ} (a : ℝ)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hd : ∀ x, HasDerivAt d (4*f x-a*f x^2) x)
    (hf2 : Integrable (fun x => f x^2)) (hd2 : Integrable (fun x => d x^2))
    (hf3 : Integrable (fun x => f x^3)) (x : ℝ) :
    d x^2-4*f x^2+(2*a/3)*f x^3=0 := by
  -- This conserved polynomial is integrable; no asymptotic derivative assumption is needed.
  let W (y : ℝ) := d y^2-4*f y^2+(2*a/3)*f y^3
  have hW (y : ℝ) : HasDerivAt W 0 y := by
    convert (((hd y).pow 2).sub (((hf y).pow 2).const_mul 4)).add
      (((hf y).pow 3).const_mul (2*a/3)) using 1
    ring
  have hconst (y : ℝ) : W y=W 0 := is_const_of_deriv_eq_zero
    (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv) y 0
  have hi : Integrable W := (hd2.sub (hf2.const_mul 4)).add (hf3.const_mul (2*a/3))
  have hc : Integrable (fun _ : ℝ => W 0) := hi.congr (Eventually.of_forall hconst)
  have hz : W 0=0 := by simpa only [integrable_const_iff,isFiniteMeasure_iff,
    Real.volume_univ,lt_self_iff_false,or_false] using hc
  exact (hconst x).trans hz

/-- The positive decaying semilinear solution has the forced peak 6/a.
Use: supplies the exact initial height and zero slope for profile uniqueness.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: a nonzero nonnegative continuous function vanishing at both ends
attains a positive maximum. Its derivative is zero there, so the zero first
integral determines the positive height algebraically. -/
theorem semilinear_peak {f d : ℝ → ℝ} {a : ℝ} (ha : 0<a)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hd : ∀ x, HasDerivAt d (4*f x-a*f x^2) x)
    (hf2 : Integrable (fun x => f x^2)) (hd2 : Integrable (fun x => d x^2))
    (hf3 : Integrable (fun x => f x^3))
    (ht : Tendsto f atTop (𝓝 0)) (hb : Tendsto f atBot (𝓝 0))
    (hn : ∃ z, 0<f z) : ∃ b, f b=6/a ∧ d b=0 := by
  -- Vanishing at both ends makes a positive maximum an actual finite point.
  obtain ⟨z,hz⟩ := hn
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hlim : Tendsto f (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨hb,ht⟩
  obtain ⟨b,hmax⟩ := hfc.exists_forall_ge' z
    ((hlim.eventually (Iio_mem_nhds hz)).mono fun _ h => h.le)
  have hp : 0<f b := hz.trans_le (hmax z)
  have hm : IsLocalMax f b := (show IsMaxOn f univ b from fun _ _ => hmax _).isLocalMax univ_mem
  have hdb : d b=0 := hm.hasDerivAt_eq_zero (hf b)
  have hw := semilinear_first_integral a hf hd hf2 hd2 hf3 b
  rw [hdb] at hw
  have hab : a*f b=6 := by nlinarith [sq_pos_of_pos hp]
  refine ⟨b,?_,hdb⟩
  apply (eq_div_iff ha.ne').mpr
  linarith

end
end jacobi.Young
