import jacobi.Jacobi.StandardEnergyFormula
import jacobi.Jacobi.StandardUniform
import jacobi.Jacobi.FibreLimit
import jacobi.Packing.ArbitrarySequence
import jacobi.Variational.Transfer

/-!
The standard realization's finite fibre and one-sided Green geometry.
All statements refer to the actual standard coefficient encoding: its
terminal polynomial, endpoint norm, conductance inverse, uniform kernel
limit, global bounds and cubic energy limit have already been proved.
Use: StandardDescent starts the exact resolvent flow at these matrices;
the common spectral mass fixes its Taylor remainder coefficient.
Article: jacobi, Theorem 5.4.
Article role: the printed Green kernel, terminal-zero uniform limit, exact standard energy and
finite-fibre upper bound.
-/
namespace jacobi.Applications
noncomputable section
open Real Set Filter jacobi.Jacobi jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The one-sided kernel has exactly the endpoint-factor form used
for the standard geometry, with r=a+1/2.
Article: jacobi, Theorem 5.4.
-/
theorem standard_kernel_diagonal_factor {a s t : ℝ} (hs : 0<s) (ht : 0<t) (hst : s≤t) :
    standardLimitKernel a s t=(s/t)^(a+1/2)*standardLimitKernel a t t := by
  have htP : 0<t^(2*a+1) := rpow_pos_of_pos ht _
  have hrP : 0<(s/t)^(2*a+1) := rpow_pos_of_pos (div_pos hs ht) _
  have hprod : s^(2*a+1)*t^(2*a+1)=(s/t)^(2*a+1)*(t^(2*a+1))^2 := by
    rw [div_rpow hs.le ht.le,pow_two]
    field_simp [htP.ne']
  have hroot : sqrt ((s/t)^(2*a+1))=(s/t)^(a+1/2) := by
    rw [sqrt_eq_rpow,← rpow_mul (div_pos hs ht).le]
    congr 1
    ring
  rw [standardLimitKernel,standardLimitKernel,max_eq_right hst,max_self,hprod,
    sqrt_mul hrP.le,sqrt_sq htP.le,hroot,sqrt_mul_self htP.le]
  ring

/-- The displayed nonzero-parameter diagonal is exactly the true
integral diagonal. Its logarithmic continuation is proved separately.
Article: jacobi, Theorem 5.4.
-/
theorem standard_diagonal_printed {a t : ℝ} (hne : a≠0) (ht : 0<t) :
    standardLimitKernel a t t=t*(1-t^(2*a))/a := by
  rw [standard_diagonal_formula hne ht]
  have hp : t*t^(2*a)=t^(2*a+1) := by
    conv_lhs => lhs; rw [← rpow_one t]
    rw [← rpow_add ht]
    congr 1
    ring
  rw [mul_sub,mul_one,hp]

/-- Full uniform standard-kernel convergence with the exact floor and
terminal zero conventions. The beta parameter affects no limit value.
Article: jacobi, Theorem 5.4.
-/
theorem standard_kernel_uniform {a b δ : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) (hδ : 0<δ) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n≥N,∀ s∈Icc δ 1,∀ t∈Icc δ 1,
      |standardGreenTail a b n (Nat.floor ((n:ℝ)*s)) (Nat.floor ((n:ℝ)*t))/(n:ℝ)-
        standardLimitKernel a s t|<ε :=
  standardGreenTail_uniform (by linarith) hb hδ

/-- The actual standard chain realizes the printed one-sided cubic
energy constant, with no asymptotic or integrability assumptions.
Article: jacobi, Theorem 5.4.
-/
theorem standard_realization_energy {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun N : ℕ => (standardChain a b (by linarith : -1<a) hb N).energy/(N:ℝ)^3)
      atTop (𝓝 (8/(3*(2*a+3)*(4*a+3)))) := standard_energy_limit ha hb

/-- The actual whole-fibre optimal energy has upper limiting value
at most the standard one-sided constant. Every finite standard chain is
a proved genuine competitor, rather than an assumed limiting candidate.
Article: jacobi, Theorem 5.4.
-/
theorem standard_fibre_upper_bound {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    limsup (fun N : ℕ => fibreEnergyInfimum (nodes a b (by linarith : -1<a) hb N)) atTop≤
      ENNReal.ofReal (8/(3*(2*a+3)*(4*a+3))) := by
  have ha' : -1<a := by linarith
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (standard_energy_limit ha hb)
  have hbnd := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun N =>
    show fibreEnergyInfimum (nodes a b ha' hb N)≤fibreCost (standardChain a b ha' hb N)
      from sInf_le ⟨_,standardChain_inFiber ha' hb N,rfl⟩))
  change Tendsto (fun N => fibreCost (standardChain a b ha' hb N)) atTop
    (𝓝 (ENNReal.ofReal (8/(3*(2*a+3)*(4*a+3))))) at hlim
  rwa [hlim.limsup_eq] at hbnd

/-- The standard chain's actual scaled resolvent trace has the exact
limiting mass, independently of its spectral weights.
Article: jacobi, Theorem 5.4.
-/
theorem standard_mass_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => jacobi.Packing.mass (standardChain a b ha hb (n+1)))
      atTop (𝓝 (1/(2*(a+1)))) := by
  let S n := nodes a b ha hb (n+1)
  let J n := standardChain a b ha hb (n+1)
  have hJ n : InFiber (J n) (S n).polynomial := standardChain_inFiber ha hb (n+1)
  have h := jacobi.Packing.arbitrary_mass_limit (fun n => n+1) J
    (fun n => (S n).contractive (hJ n)) (jacobi.Bessel.edgeSpectrum a ha)
    (arbitrary_fibre_spectral_limit ha hb J hJ)
  rwa [jacobi.Bessel.edgeSpectrum_mass ha] at h

end
end jacobi.Applications
