import jacobi.Reference.Hypergeometric
import Mathlib.Analysis.Analytic.Order

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The regular analytic solution of Gauss's equation is determined by its
value at zero when Re(c)>0. This is the uniqueness step used to prove
Euler's transformation and the cosine hypergeometric representation in
the literal beta-integral proof.
Source: the Frobenius indicial equation, proved here for actual analytic
functions using mathlib's analytic order and genuine derivatives.
Use: computes the leading indicial coefficient in gauss_zero_unique without a formal-series or derivative assumption.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Multiplying a genuine derivative of z^n*u(z) by z removes the apparent negative power at n=0.
Use: computes the leading indicial coefficient in gauss_zero_unique without a formal-series or derivative assumption.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Source: the ordinary product rule and the Euler differential operator z*d/dz.
Proof: the constant-power case is direct; for a successor degree the
ordinary derivative has nonnegative powers, and multiplication by z
restores the common original degree. -/
theorem euler_power_derivative {u : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℂ u z) (n : ℕ) :
    z*deriv (fun w : ℂ => w^n*u w) z=z^n*((n:ℂ)*u z+z*deriv u z) := by
  -- Split off the constant degree so every remaining product-rule power is nonnegative.
  cases n with
  | zero => simp only [pow_zero,one_mul,Nat.cast_zero,zero_mul,zero_add]
  | succ n =>
    have hd := ((hasDerivAt_id z).pow (n+1)).mul hu.hasDerivAt
    have he : deriv (fun w : ℂ => w^(n+1)*u w) z=
        (n+1:ℂ)*z^n*u z+z^(n+1)*deriv u z := by
      convert! hd.deriv using 1
      simp [Nat.cast_add,Nat.cast_one]
    rw [he,pow_succ]
    push_cast
    ring

/-- An actual analytic solution of the regular Gauss equation with zero initial value vanishes on a neighborhood of zero.
Use: fixes the original hypergeometric solution in the Euler and cosine transformations needed for the beta-integral identity.
Article: jacobi, Lemma C.1.
Source: Frobenius uniqueness with indicial coefficient n*(n-1+c), proved here.
Proof: if the derivative has finite vanishing order m, factor it as
z^m*u with u(0) nonzero and factor the original function as z^(m+1)*v.
The actual differential equation, after cancelling z^m away from zero,
has limit (m+c)*u(0)=0. Its real-part positivity contradicts u(0) nonzero.
Infinite derivative order gives an identically zero analytic germ. -/
theorem gauss_zero_unique {f : ℂ → ℂ} {c d e : ℂ} (hc : 0<c.re)
    (hf : AnalyticAt ℂ f 0) (hzero : f 0=0)
    (heq : ∀ᶠ z : ℂ in 𝓝 0,
      z*(1-z)*deriv (deriv f) z+(c-d*z)*deriv f z-e*f z=0) :
    f=ᶠ[𝓝 0] 0 := by
  -- Actual analytic orders supply convergent local factorizations of the same function and derivative.
  have horder : analyticOrderAt (deriv f) 0+1=analyticOrderAt f 0 := by
    simpa only [hzero,sub_zero] using hf.analyticOrderAt_deriv_add_one
  by_cases ht : analyticOrderAt (deriv f) 0=⊤
  · exact analyticOrderAt_eq_top.mp (by simpa only [ht,top_add] using horder.symm)
  obtain ⟨m,hm⟩ : ∃ m : ℕ,analyticOrderAt (deriv f) 0=m :=
    ⟨(analyticOrderAt (deriv f) 0).toNat,(ENat.natCast_toNat ht).symm⟩
  have hfm : analyticOrderAt f 0=(m+1:ℕ) := by rw [← horder,hm]; norm_cast
  obtain ⟨u,hu,hu0,hfu⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf.deriv).mp hm
  obtain ⟨v,hv,_,hfv⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).mp hfm
  have hfu' : deriv f=ᶠ[𝓝 (0:ℂ)] (fun z : ℂ => z^m*u z) := by
    filter_upwards [hfu] with z hz
    simpa only [sub_zero,smul_eq_mul] using hz
  have hfv' : f=ᶠ[𝓝 (0:ℂ)] (fun z : ℂ => z^(m+1)*v z) := by
    filter_upwards [hfv] with z hz
    simpa only [sub_zero,smul_eq_mul] using hz
  let R : ℂ → ℂ := fun z =>
    (1-z)*((m:ℂ)*u z+z*deriv u z)+(c-d*z)*u z-e*z*v z
  have hR : ContinuousAt R 0 := by
    exact (((continuousAt_const.sub continuousAt_id).mul
      ((continuousAt_const.mul hu.continuousAt).add (continuousAt_id.mul hu.deriv.continuousAt))).add
        ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul hu.continuousAt)).sub
          ((continuousAt_const.mul continuousAt_id).mul hv.continuousAt)
  have hRzero : R=ᶠ[𝓝[≠] (0:ℂ)] 0 := by
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
      hfu'.filter_mono nhdsWithin_le_nhds,hfv'.filter_mono nhdsWithin_le_nhds,
      hfu'.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds,
      hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with z hz hzu hzv hlocal hdu hz0
    have hdiff : deriv (deriv f) z=deriv (fun w : ℂ => w^m*u w) z := hlocal.deriv_eq
    have hEuler := euler_power_derivative hdu.differentiableAt m
    have hres : z^m*R z=0 := by
      dsimp [R]
      rw [hdiff,hzu,hzv] at hz
      rw [pow_succ] at hz
      linear_combination hz-(1-z)*hEuler
    exact (mul_eq_zero.mp hres).resolve_left (pow_ne_zero m hz0)
  have hlim : R 0=0 := tendsto_nhds_unique
    (hR.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' hRzero.symm)
  have hcz : (m:ℂ)+c≠0 := by
    have hp : 0<((m:ℂ)+c).re := by simp only [add_re,natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) m]
    intro hz; rw [hz,zero_re] at hp; exact lt_irrefl _ hp
  have hprod : ((m:ℂ)+c)*u 0=0 := by
    simp only [R,mul_zero,zero_mul,sub_zero,one_mul] at hlim
    linear_combination hlim
  exact False.elim (hu0 ((mul_eq_zero.mp hprod).resolve_left hcz))

end
end jacobi.Reference.Hypergeometric
