import polyak.Boundary.P1.LocalExpansion
import polyak.Spiral.Factor
import chebyshev2.Calculus.ImplicitScalar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Analytic.Linear

/-!
Article: Appendix C, expansions at q↓0.
Use: compactify the true factor as R=ρ/q, so the implicit equation is
nonsingular at q=0 and R=1+√2. The P₁ and spiral equations are treated by one
analytic construction; their difference has an exact factor q² before returning to ρ.
-/
namespace polyak.Asymptotics.SmallQ
noncomputable section
open Filter Set
open scoped Topology ContDiff

/-- The leading factor in both small-condition-number expansions. -/
def leading : ℝ := 1+Real.sqrt 2

def second : ℝ := 2+3*Real.sqrt 2/2

def excess : ℝ := (10+7*Real.sqrt 2)/4

theorem sqrt_two_pos : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem leading_pos : 0<leading := by unfold leading; positivity

theorem leading_equation : leading^2-2*leading-1=0 := by
  have hh:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  unfold leading
  nlinarith

/-- The reciprocal-cosh parameter of a factor ρ=qR. -/
def compactParameter (q R : ℝ) : ℝ := 2*q*R/(1+(q*R)^2)

/-- A denominator-free form of R²−2uR−1=0 with u=1−z/2+z²A(z). -/
def sourceEquation (A : ℝ → ℝ) (p : ℝ×ℝ) : ℝ :=
  (p.2^2-2*p.2-1)*(1+(p.1*p.2)^2)^2+
    2*p.1*p.2^2*(1+(p.1*p.2)^2)-
      8*p.1^2*p.2^3*A (compactParameter p.1 p.2)

theorem sourceEquation_zero (A : ℝ → ℝ) (R : ℝ) :
    sourceEquation A (0,R)=R^2-2*R-1 := by simp [sourceEquation]

/-- A genuine analytic root with the local uniqueness supplied by the implicit function theorem. -/
structure RescaledBranch (A : ℝ → ℝ) where
  r : ℝ → ℝ
  analytic : AnalyticAt ℝ r 0
  initial : r 0=leading
  equation : ∀ᶠ q in 𝓝 (0 : ℝ),sourceEquation A (q,r q)=0
  unique : ∀ᶠ p in 𝓝 ((0 : ℝ),leading),sourceEquation A p=0 ↔ r p.1=p.2

/-- The actual source equation has a nonsingular analytic branch at the compactified endpoint. -/
theorem exists_rescaledBranch (A : ℝ → ℝ) (hA : AnalyticAt ℝ A 0) :
    Nonempty (RescaledBranch A) := by
  have hx : AnalyticAt ℝ (Prod.fst : ℝ×ℝ → ℝ) (0,leading) :=
    (contDiffAt_fst : ContDiffAt ℝ ω (Prod.fst : ℝ×ℝ → ℝ) (0,leading)).analyticAt
  have hy : AnalyticAt ℝ (Prod.snd : ℝ×ℝ → ℝ) (0,leading) :=
    (contDiffAt_snd : ContDiffAt ℝ ω (Prod.snd : ℝ×ℝ → ℝ) (0,leading)).analyticAt
  have hz : AnalyticAt ℝ (fun p : ℝ×ℝ => compactParameter p.1 p.2) (0,leading) := by
    unfold compactParameter
    fun_prop (disch := norm_num)
  have hAc : AnalyticAt ℝ (fun p : ℝ×ℝ => A (compactParameter p.1 p.2)) (0,leading) :=
    hA.comp_of_eq hz (by simp [compactParameter])
  have hf : ContDiffAt ℝ ω (sourceEquation A) (0,leading) := by
    have hg : AnalyticAt ℝ (fun p : ℝ×ℝ =>
        (p.2^2-2*p.2-1)*(1+(p.1*p.2)^2)^2) (0,leading) := by fun_prop
    have hh : AnalyticAt ℝ (fun p : ℝ×ℝ =>
        2*p.1*p.2^2*(1+(p.1*p.2)^2)) (0,leading) := by fun_prop
    have hi : AnalyticAt ℝ (fun p : ℝ×ℝ => 8*p.1^2*p.2^3) (0,leading) := by fun_prop
    exact ((hg.add hh).sub (hi.mul hAc)).contDiffAt
  have hv : HasDerivAt (fun R => sourceEquation A (0,R)) (2*Real.sqrt 2) leading := by
    have hh:=(((hasDerivAt_id leading).pow 2).sub ((hasDerivAt_id leading).const_mul 2)).sub_const 1
    convert hh using 1
    · funext R
      exact sourceEquation_zero A R
    · simp only [leading,id_eq]
      ring
  have hd:=chebyshev2.Calculus.scalar_derivative_invertible
    (hf.differentiableAt (by simp)) hv (by positivity : 2*Real.sqrt (2 : ℝ)≠0)
  have hn : (ω : ℕ∞ω)≠0 := by simp
  let g:=hf.implicitFunction hn hd
  have hroot : sourceEquation A (0,leading)=0 := by rw [sourceEquation_zero,leading_equation]
  refine ⟨⟨g,(hf.contDiffAt_implicitFunction hn hd).analyticAt,
    hf.implicitFunction_apply_self hn hd,?_,?_⟩⟩
  · simpa only [hroot,g] using hf.eventually_apply_implicitFunction hn hd
  · simpa only [hroot,g] using hf.eventually_apply_eq_iff_implicitFunction hn hd

/-- The selected local branch is constructed analytically from the original equation. -/
def rescaledBranch (A : ℝ → ℝ) (hA : AnalyticAt ℝ A 0) : RescaledBranch A :=
  Classical.choice (exists_rescaledBranch A hA)

/-- The exact equation after reintroducing the physical u and the positive denominator. -/
theorem sourceEquation_physical (A : ℝ → ℝ) (q R : ℝ) :
    sourceEquation A (q,R)=(1+(q*R)^2)^2*
      (R^2-2*(1-compactParameter q R/2+(compactParameter q R)^2*A (compactParameter q R))*R-1) := by
  have hd : 1+(q*R)^2≠0 := by positivity
  unfold sourceEquation compactParameter
  field_simp
  ring

/-- The zero-reserve branch is the original spiral polynomial, with exact clearing factors. -/
theorem sourceEquation_spiral (q R : ℝ) :
    q^2*sourceEquation (fun _ => 0) (q,R)=
      (1+(q*R)^2)*Spiral.spiralPolynomial (q*R) q := by
  unfold sourceEquation Spiral.spiralPolynomial
  ring

/-- Both source families have the same exact first derivative of ρ/q. -/
theorem leading_second_equation :
    (2*leading-2)*(-second)+2*leading^2=0 := by
  have hh:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  unfold leading second
  nlinarith

theorem RescaledBranch.hasDerivAt {A : ℝ → ℝ} (b : RescaledBranch A)
    (hA : AnalyticAt ℝ A 0) : HasDerivAt b.r (-second) 0 := by
  let d:=deriv b.r 0
  have hba:=b.analytic
  have hr : HasDerivAt b.r d 0:=b.analytic.differentiableAt.hasDerivAt
  have hq:=hasDerivAt_id (0 : ℝ)
  have hz : AnalyticAt ℝ (fun q => compactParameter q (b.r q)) 0 := by
    unfold compactParameter
    fun_prop (disch := simp)
  have hAc : AnalyticAt ℝ (fun q => A (compactParameter q (b.r q))) 0 :=
    hA.comp_of_eq hz (by simp [compactParameter])
  have hD:=((hq.mul hr).pow 2).const_add 1
  have hfirst:=((((hr.pow 2).sub (hr.const_mul 2)).sub_const 1).mul (hD.pow 2))
  have hsecond:=(((hq.const_mul 2).mul (hr.pow 2)).mul hD)
  have hthird:=((((hq.pow 2).const_mul 8).mul (hr.pow 3)).mul hAc.differentiableAt.hasDerivAt)
  have hf : HasDerivAt (fun q => sourceEquation A (q,b.r q))
      ((2*leading-2)*d+2*leading^2) 0 := by
    convert (hfirst.add hsecond).sub hthird using 1
    · funext q
      rfl
    · norm_num [b.initial]
      ring
  have hc:=hf.congr_of_eventuallyEq
    (show (fun _ : ℝ => (0 : ℝ))=ᶠ[𝓝 0] (fun q => sourceEquation A (q,b.r q)) from
      b.equation.mono (fun _ he => he.symm))
  have hd0:=hc.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hd : d= -second := by
    have he : (2*leading-2)*d=(2*leading-2)*(-second) := by
      linarith [leading_second_equation]
    have hpos : 0<2*leading-2 := by unfold leading; linarith [sqrt_two_pos]
    exact mul_left_cancel₀ hpos.ne' he
  simpa only [hd] using hr

/-- The first printed rate expansion, with a genuine cubic remainder. -/
theorem RescaledBranch.factor_expansion {A : ℝ → ℝ} (b : RescaledBranch A)
    (hA : AnalyticAt ℝ A 0) :
    (fun q => q*b.r q-(leading*q-second*q^2))=O[𝓝 0] (fun q : ℝ => q^3) := by
  have hh:=polyak.Asymptotics.analytic_first_order b.analytic (b.hasDerivAt hA)
  have hm:=(Asymptotics.isBigO_refl (fun q : ℝ => q) (𝓝 0)).mul hh
  convert hm using 1
  · funext q
    rw [b.initial]
    ring
  · funext q
    ring

/-- Polynomial divided powers, with no division at coincident roots. -/
def dividedPower (n : ℕ) (R S : ℝ) : ℝ :=
  ∑ k∈Finset.range n,R^(n-1-k)*S^k

/-- Exact divided difference of the zero-reserve source equation. -/
def dividedEquation (q R S : ℝ) : ℝ :=
  dividedPower 2 R S-2+2*q*dividedPower 2 R S+
    2*q^2*dividedPower 4 R S-4*q^2*dividedPower 3 R S-2*q^2*dividedPower 2 R S+
    2*q^3*dividedPower 4 R S+q^4*dividedPower 6 R S-
      2*q^4*dividedPower 5 R S-q^4*dividedPower 4 R S

theorem dividedEquation_exact (q R S : ℝ) :
    sourceEquation (fun _ => 0) (q,R)-sourceEquation (fun _ => 0) (q,S)=
      (R-S)*dividedEquation q R S := by
  unfold sourceEquation dividedEquation dividedPower
  norm_num [Finset.sum_range_succ]
  ring

theorem dividedEquation_zero (R S : ℝ) : dividedEquation 0 R S=R+S-2 := by
  norm_num [dividedEquation,dividedPower,Finset.sum_range_succ]

theorem dividedEquation_initial : dividedEquation 0 leading leading=2*Real.sqrt 2 := by
  rw [dividedEquation_zero]
  unfold leading
  ring

/-- The analytic exact quotient of the two rescaled roots after the q² factor. -/
def branchExcess {A : ℝ → ℝ} (b : RescaledBranch A) (s : RescaledBranch (fun _ => 0)) (q : ℝ) : ℝ :=
  8*(b.r q)^3*A (compactParameter q (b.r q))/dividedEquation q (b.r q) (s.r q)

theorem branchExcess_analyticAt {A : ℝ → ℝ} (b : RescaledBranch A)
    (s : RescaledBranch (fun _ => 0)) (hA : AnalyticAt ℝ A 0) :
    AnalyticAt ℝ (branchExcess b s) 0 := by
  have hb:=b.analytic
  have hs:=s.analytic
  have hz : AnalyticAt ℝ (fun q => compactParameter q (b.r q)) 0 := by
    unfold compactParameter
    fun_prop (disch := simp)
  have hAc:=hA.comp_of_eq hz (by simp [compactParameter])
  have hd : AnalyticAt ℝ (fun q => dividedEquation q (b.r q) (s.r q)) 0 := by
    unfold dividedEquation dividedPower
    fun_prop
  have hd0 : dividedEquation 0 (b.r 0) (s.r 0)≠0 := by
    rw [b.initial,s.initial,dividedEquation_initial]
    positivity
  have hn : AnalyticAt ℝ (fun q => 8*(b.r q)^3*A (compactParameter q (b.r q))) 0 := by
    exact ((analyticAt_const.mul (hb.pow 3)).mul hAc)
  exact hn.div hd hd0

/-- The comparison is an exact analytic identity before any asymptotic truncation. -/
theorem branch_difference_exact {A : ℝ → ℝ} (b : RescaledBranch A)
    (s : RescaledBranch (fun _ => 0)) :
    ∀ᶠ q in 𝓝 (0 : ℝ),b.r q-s.r q=q^2*branchExcess b s q := by
  have hb:=b.analytic.continuousAt
  have hs:=s.analytic.continuousAt
  have hd : ContinuousAt (fun q => dividedEquation q (b.r q) (s.r q)) 0 := by
    unfold dividedEquation dividedPower
    fun_prop
  have hd0 : dividedEquation 0 (b.r 0) (s.r 0)≠0 := by
    rw [b.initial,s.initial,dividedEquation_initial]
    positivity
  filter_upwards [b.equation,s.equation,hd.eventually_ne hd0] with q hq hs hne
  have he:=dividedEquation_exact q (b.r q) (s.r q)
  have hA : sourceEquation A (q,b.r q)=sourceEquation (fun _ => 0) (q,b.r q)-
      8*q^2*(b.r q)^3*A (compactParameter q (b.r q)) := by unfold sourceEquation; ring
  rw [hs] at he
  rw [hA] at hq
  unfold branchExcess
  rw [←mul_div_assoc]
  apply (eq_div_iff hne).mpr
  linarith

/-- The cubic excess coefficient is exactly the printed algebraic number. -/
theorem branchExcess_zero {A : ℝ → ℝ} (b : RescaledBranch A)
    (s : RescaledBranch (fun _ => 0)) (hA : A 0=1/8) : branchExcess b s 0=excess := by
  have hs2:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hs3 : (Real.sqrt (2 : ℝ))^3=2*Real.sqrt 2 := by
    calc
      _ = Real.sqrt 2*(Real.sqrt 2)^2 := by ring
      _ = _ := by rw [hs2]; ring
  unfold branchExcess
  rw [b.initial,s.initial]
  norm_num [compactParameter,hA,dividedEquation_initial]
  unfold leading excess
  field_simp
  nlinarith [hs2,hs3]

/-- The complete printed cubic difference, with a genuine quartic remainder. -/
theorem branch_difference_expansion {A : ℝ → ℝ} (b : RescaledBranch A)
    (s : RescaledBranch (fun _ => 0)) (hA : AnalyticAt ℝ A 0) (hA0 : A 0=1/8) :
    (fun q => q*b.r q-q*s.r q-excess*q^3)=O[𝓝 0] (fun q : ℝ => q^4) := by
  have hd:=(branchExcess_analyticAt b s hA).differentiableAt.hasDerivAt.isBigO_sub
  rw [branchExcess_zero b s hA0] at hd
  have hm:=(Asymptotics.isBigO_refl (fun q : ℝ => q^3) (𝓝 0)).mul hd
  apply hm.congr' ?_ ?_
  · filter_upwards [branch_difference_exact b s] with q hq
    change q^3*(branchExcess b s q-excess)=q*b.r q-q*s.r q-excess*q^3
    symm
    calc
      q*b.r q-q*s.r q-excess*q^3=q*(b.r q-s.r q)-excess*q^3 := by ring
      _ = q^3*(branchExcess b s q-excess) := by rw [hq]; ring
  · exact Eventually.of_forall (fun q => by dsimp; ring)

end
end polyak.Asymptotics.SmallQ
