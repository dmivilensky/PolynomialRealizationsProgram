import jacobi.Reference.EulerTransformation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Article: jacobi, Proposition C.4.
The actual cosine is identified with the convergent Chebyshev Gauss
function on the full interval before pi. A genuine differential equation
and analytic initial-value uniqueness prove the identity; the functions
are never replaced by an assumed special-function formula.
Source: the trigonometric hypergeometric representation, DLMF 15.4.12.
Use: proves cosine_hypergeometric from the actual Gauss differential equation after the trigonometric substitution.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An analytic solution of a constant-coefficient second-order equation with zero value and derivative at zero vanishes near zero.
Use: proves cosine_hypergeometric from the actual Gauss differential equation after the trigonometric substitution.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: uniqueness for the analytic second-order initial-value problem.
Proof: differentiate the genuine local equation n times to obtain
the exact recurrence D^(n+2)f=A*D^n f. Both initial derivatives vanish,
so every derivative vanishes. The analytic order is therefore infinite,
which means that the same actual function vanishes on a neighborhood. -/
theorem constant_ode_zero {f : ℂ → ℂ} {A : ℂ} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0=0) (h1 : deriv f 0=0)
    (heq : deriv (deriv f)=ᶠ[𝓝 (0:ℂ)] (fun z => A*f z)) : f=ᶠ[𝓝 (0:ℂ)] 0 := by
  -- The derivative recurrence follows from the actual local equality, not formal differentiation of an unproved series.
  have hrec (n : ℕ) : iteratedDeriv (n+2) f 0=A*iteratedDeriv n f 0 := by
    rw [show n+2=(n+1)+1 by omega,iteratedDeriv_succ',iteratedDeriv_succ',
      heq.iteratedDeriv_eq n,iteratedDeriv_const_mul_field]
  have hvan (n : ℕ) : iteratedDeriv n f 0=0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n
      · exact h0
      · change iteratedDeriv 1 f 0=0
        rw [iteratedDeriv_one]
        exact h1
      · rw [show n+1+1=n+2 by omega,hrec,ih n (by omega),mul_zero]
  apply analyticOrderAt_eq_top.mp
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr (fun i _ => hvan i)

/-- The complex trigonometric argument in the exact Chebyshev-to-Gauss substitution.
Use: proves the cosine representation before beta convolution and controls its physical convergence interval.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def cosineArgument (z : ℂ) : ℂ := (1-Complex.cos z)/2

/-- The actual complex trigonometric argument and its first derivative are analytic and genuinely differentiate to their printed values.
Use: computes both true chain derivatives in cosine_equation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: use the community entire cosine and its ordinary derivative. -/
theorem cosineArgument_hasDerivAt (z : ℂ) :
    HasDerivAt cosineArgument (Complex.sin z/2) z := by
  convert! ((hasDerivAt_const z (1:ℂ)).sub (Complex.hasDerivAt_cos z)).div_const 2 using 1
  simp

/-- The actual Gauss cosine composition satisfies the exact harmonic equation wherever its true argument lies inside the unit disk.
Use: regular analytic initial-value uniqueness identifies this actual composition with the cosine.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the genuine Gauss composition twice. The
identities x*(1-x)=sin(theta)^2/4 and 1/2-x=cos(theta)/2 turn
Gauss's equation at a=-lambda,b=lambda,c=1/2 into H''=-lambda^2*H. -/
theorem cosine_equation (lam : ℂ) {z : ℂ} (hz : ‖cosineArgument z‖<1) :
    let H : ℂ → ℂ := fun w => ordinaryHypergeometric (-lam) lam (1/2:ℂ) (cosineArgument w)
    deriv (deriv H) z= -lam^2*H z := by
  -- The second chain derivative uses the same actual Gauss function and its proved analytic derivative.
  let U : ℂ → ℂ := ordinaryHypergeometric (-lam) lam (1/2:ℂ)
  let H : ℂ → ℂ := fun w => U (cosineArgument w)
  let S : ℂ → ℂ := fun w => deriv U (cosineArgument w)*(Complex.sin w/2)
  have hc : Continuous cosineArgument := by unfold cosineArgument; fun_prop
  have hU (w : ℂ) (hw : ‖cosineArgument w‖<1) : AnalyticAt ℂ U (cosineArgument w) := analytic hw
  have hH (w : ℂ) (hw : ‖cosineArgument w‖<1) : HasDerivAt H (S w) w :=
    HasDerivAt.comp (h₂ := U) (h := cosineArgument) w
      (hU w hw).differentiableAt.hasDerivAt (cosineArgument_hasDerivAt w)
  have hS := ((hU z hz).deriv.differentiableAt.hasDerivAt.comp z
    (cosineArgument_hasDerivAt z)).mul ((Complex.hasDerivAt_sin z).div_const 2)
  change HasDerivAt S _ z at hS
  have hlocal : deriv H=ᶠ[𝓝 z] S := by
    filter_upwards [(hc.norm.continuousAt.eventually (Iio_mem_nhds hz))] with w hw
    exact (hH w hw).deriv
  change deriv (deriv H) z= -lam^2*H z
  rw [hlocal.deriv_eq,hS.deriv]
  have heq := equation (a := -lam) (b := lam) (c := (1/2:ℂ)) (by norm_num) hz
  change cosineArgument z*(1-cosineArgument z)*deriv (deriv U) (cosineArgument z)+
    ((1/2:ℂ)-(-lam+lam+1)*cosineArgument z)*deriv U (cosineArgument z)-(-lam)*lam*U (cosineArgument z)=0 at heq
  have hx : cosineArgument z*(1-cosineArgument z)=(Complex.sin z/2)^2 := by
    unfold cosineArgument
    linear_combination -(Complex.sin_sq_add_cos_sq z)/4
  have hfirst : (1/2:ℂ)-cosineArgument z=Complex.cos z/2 := by unfold cosineArgument; ring
  dsimp [H]
  rw [show -lam+lam+1=(1:ℂ) by ring,one_mul,hx,hfirst] at heq
  linear_combination heq

/-- On the original positive angular interval the genuine hypergeometric cosine composition is exactly cos(lambda*theta).
Use: beta_convolution integrates this actual cosine representation in the defining reference integral.
Article: jacobi, Lemma C.1.
Source: DLMF 15.4.12, proved here by the actual Gauss equation and analytic uniqueness.
Proof: near zero the two actual analytic functions solve the same
constant-coefficient equation and have initial state (1,0). Their
difference vanishes by constant_ode_zero. Analytic continuation along
the real angular segment, on which the original Gauss series converges,
gives equality at every theta before pi. -/
theorem cosine_hypergeometric (lam : ℂ) {theta : ℝ}
    (htheta : theta∈Ico (0:ℝ) Real.pi) :
    ordinaryHypergeometric (-lam) lam (1/2:ℂ) (cosineArgument (theta:ℂ))=
      Complex.cos (lam*(theta:ℂ)) := by
  -- The continuation set is the true real segment; no convergence claim outside the original Gauss disk is needed.
  let U : ℂ → ℂ := ordinaryHypergeometric (-lam) lam (1/2:ℂ)
  let H : ℂ → ℂ := fun w => U (cosineArgument w)
  let C : ℂ → ℂ := fun w => Complex.cos (lam*w)
  let D : ℂ → ℂ := fun w => -Complex.sin (lam*w)*lam
  have hc (w : ℂ) : AnalyticAt ℂ cosineArgument w := by unfold cosineArgument; fun_prop
  have hH (w : ℂ) (hw : ‖cosineArgument w‖<1) : AnalyticAt ℂ H w :=
    (analytic hw).comp (hc w)
  have hC (w : ℂ) : AnalyticAt ℂ C w := by dsimp [C]; fun_prop
  have hC1 (w : ℂ) : HasDerivAt C (D w) w := by
    convert! (Complex.hasDerivAt_cos (lam*w)).comp w ((hasDerivAt_id w).const_mul lam) using 1
    dsimp [C,D]
    ring
  have hC2 (w : ℂ) : HasDerivAt D (-lam^2*C w) w := by
    convert! (((Complex.hasDerivAt_sin (lam*w)).comp w ((hasDerivAt_id w).const_mul lam)).neg).mul_const lam using 1
    dsimp [C,D]
    ring
  have harg0 : cosineArgument 0=0 := by simp [cosineArgument]
  have hnear : H-C=ᶠ[𝓝 (0:ℂ)] 0 := by
    have hH0 := hH 0 (by rw [harg0,norm_zero]; norm_num)
    apply constant_ode_zero (hH0.sub (hC 0))
    · simp [H,C,U,harg0]
    · rw [deriv_sub hH0.differentiableAt (hC 0).differentiableAt]
      have hh : HasDerivAt H (0:ℂ) 0 := by
        have hcomp := HasDerivAt.comp (h₂ := U) (h := cosineArgument) 0
          (analytic (a := -lam) (b := lam) (c := (1/2:ℂ)) (by rw [harg0,norm_zero]; norm_num)).differentiableAt.hasDerivAt
            (cosineArgument_hasDerivAt 0)
        convert! hcomp using 1
        simp only [Complex.sin_zero,zero_div,mul_zero]
      rw [hh.deriv,(hC1 0).deriv]
      simp [D]
    · filter_upwards [(hc 0).continuousAt.norm.eventually
        (Iio_mem_nhds (show ‖cosineArgument 0‖<1 by rw [harg0,norm_zero]; norm_num))] with w hw
      have hlocal : deriv (H-C)=ᶠ[𝓝 w] (deriv H-deriv C) := by
        filter_upwards [(hc w).continuousAt.norm.eventually (Iio_mem_nhds hw)] with v hv
        exact deriv_sub (hH v hv).differentiableAt (hC v).differentiableAt
      rw [hlocal.deriv_eq,deriv_sub (hH w hw).deriv.differentiableAt (hC w).deriv.differentiableAt]
      have hfun : deriv C=D := funext (fun v => (hC1 v).deriv)
      rw [hfun,(hC2 w).deriv,cosine_equation lam hw]
      change -lam^2*H w- -lam^2*C w= -lam^2*(H w-C w)
      ring
  have hbound (s : ℝ) (hs : s∈Icc 0 theta) : ‖cosineArgument (s:ℂ)‖<1 := by
    have hs' : s∈Icc (0:ℝ) Real.pi := ⟨hs.1,hs.2.trans htheta.2.le⟩
    have hcos := Real.strictAntiOn_cos hs' ⟨Real.pi_pos.le,le_rfl⟩ (hs.2.trans_lt htheta.2)
    rw [Real.cos_pi] at hcos
    have he : cosineArgument (s:ℂ)=(((1-Real.cos s)/2:ℝ):ℂ) := by simp [cosineArgument]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [Real.cos_le_one s] : 0≤(1-Real.cos s)/2)]
    linarith
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) theta
  have hA : AnalyticOnNhd ℂ (H-C) S := by
    rintro w ⟨s,hs,rfl⟩
    exact (hH _ (hbound s hs)).sub (hC _)
  have hS : IsPreconnected S := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hzero : (0:ℂ)∈S := ⟨0,⟨le_rfl,htheta.1⟩,Complex.ofReal_zero⟩
  have hend : (theta:ℂ)∈S := ⟨theta,⟨htheta.1,le_rfl⟩,rfl⟩
  exact sub_eq_zero.mp (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hS hzero hnear hend)

end
end jacobi.Reference.Hypergeometric
