import polyak.FareyPlateau.Symbols.QuadraticRemoval
import polyak.FareyPlateau.Symbols.Bezout

/-! The exact removable function R of Definition admissible.  Its contact
value and continuity are consequences of the two phase-floor jets. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Set Polynomial
open scoped BigOperators
variable {I : Type*} [Fintype I]

def contactDifference (n : I→ℤ) (w : I→ℝ) (c₀ h₀ D c : ℝ) : ℝ :=
  h₀+(1+D)*(c-c₀)-psi n w c

def curvatureQuotient (n : I→ℤ) (w : I→ℝ) (c₀ h₀ D : ℝ) : ℝ→ℝ :=
  quadraticQuotient (contactDifference n w c₀ h₀ D) c₀

theorem contactDifference_jets (n : I→ℤ) (w : I→ℝ) {c₀ h₀ D : ℝ}
    (hψ : AnalyticAt ℝ (psi n w) c₀) (hv : psi n w c₀=h₀)
    (hd : deriv (psi n w) c₀=1+D) :
    contactDifference n w c₀ h₀ D c₀=0 ∧
      deriv (contactDifference n w c₀ h₀ D) c₀=0 := by
  refine ⟨by simp [contactDifference,hv],?_⟩
  have he := ((hasDerivAt_const c₀ h₀).add
    (((hasDerivAt_id c₀).sub_const c₀).const_mul (1+D))).sub hψ.differentiableAt.hasDerivAt
  have hder := he.deriv
  change deriv (contactDifference n w c₀ h₀ D) c₀=_ at hder
  rw [hder,hd]
  ring

theorem curvatureQuotient_off_contact (n : I→ℤ) (w : I→ℝ) {c₀ h₀ D c : ℝ}
    (hψ : AnalyticAt ℝ (psi n w) c₀) (hv : psi n w c₀=h₀)
    (hd : deriv (psi n w) c₀=1+D) (hc : c≠c₀) :
    curvatureQuotient n w c₀ h₀ D c=
      (h₀+(1+D)*(c-c₀)-psi n w c)/(c-c₀)^2 := by
  obtain ⟨h0,h1⟩ := contactDifference_jets n w hψ hv hd
  exact quadraticQuotient_eq h0 h1 hc

theorem curvatureQuotient_continuousOn (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : SupportBezout n w) {c₀ h₀ D : ℝ} (hc₀ : c₀∈Icc (-1:ℝ) 1) :
    ContinuousOn (curvatureQuotient n w c₀ h₀ D) (Icc (-1:ℝ) 1) := by
  apply quadraticQuotient_continuousOn
  · exact (continuousOn_const.add ((continuousOn_id.sub continuousOn_const).const_mul (1+D))).sub
      (continuousOn_psi n w hn hw hsum hbez)
  · have hlin : AnalyticAt ℝ (fun c=>h₀+(1+D)*(c-c₀)) c₀ := by fun_prop
    exact hlin.sub (analyticAt_psi n w hn hw hsum hbez hc₀)

theorem curvatureQuotient_contact_value (n : I→ℤ) (w : I→ℝ) {c₀ h₀ D : ℝ}
    (hψ : AnalyticAt ℝ (psi n w) c₀) (hv : psi n w c₀=h₀)
    (hd : deriv (psi n w) c₀=1+D) :
    curvatureQuotient n w c₀ h₀ D c₀= -(1/2:ℝ)*deriv (deriv (psi n w)) c₀ := by
  have hlin : AnalyticAt ℝ (fun c=>h₀+(1+D)*(c-c₀)) c₀ := by fun_prop
  have hf : AnalyticAt ℝ (contactDifference n w c₀ h₀ D) c₀ := hlin.sub hψ
  obtain ⟨h0,h1⟩ := contactDifference_jets n w hψ hv hd
  rw [curvatureQuotient,quadraticQuotient_value hf h0 h1]
  have hlin_deriv : deriv (fun c=>h₀+(1+D)*(c-c₀))=(fun _=>1+D) := by
    funext c
    have ht := ((hasDerivAt_const c h₀).add
      (((hasDerivAt_id c).sub_const c₀).const_mul (1+D))).deriv
    convert ht using 1
    · congr 1
    · ring
  have he := iteratedDeriv_fun_sub (n:=2) (x:=c₀) hlin.contDiffAt hψ.contDiffAt
  change iteratedDeriv 2 (contactDifference n w c₀ h₀ D) c₀=_ at he
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,hlin_deriv,deriv_const] at he
  rw [he]
  ring

end polyak.FareyPlateau.Symbols
