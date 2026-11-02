import jacobi.Analysis.WeakSecond
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Proposition 2.2.
A continuous weak second derivative has a genuine twice continuously
differentiable primitive. The affine ambiguity is proved, rather than assumed.
Source: the fundamental theorem of calculus and the one-dimensional weak affine lemma.
Use: weak_second_regular upgrades the actual target kernel's compact-test
identity locally.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology

/-- Every continuous real forcing has an actual global C2 second primitive.
Use: weak_second_regular subtracts this primitive to reduce the weak equation
to the already proved weak affine lemma.
Article: jacobi, Proposition 2.2.
Source: the fundamental theorem of calculus, twice.
Proof: integrate from zero twice and identify both ordinary derivatives
using continuity; the derivative criterion then gives genuine C2 regularity. -/
theorem continuous_second_primitive {Q : ℝ → ℝ} (hQ : Continuous Q) :
    ∃ P : ℝ → ℝ,ContDiff ℝ 2 P ∧ ∀ x,deriv (deriv P) x=Q x := by
  let A := fun x => ∫ s in (0:ℝ)..x,Q s
  have hA (x : ℝ) : HasDerivAt A (Q x) x :=
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable _ _)
      hQ.aestronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hAd : deriv A=Q := funext fun x => (hA x).deriv
  have hA1 : ContDiff ℝ 1 A := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hA x).differentiableAt,by rw [hAd]; exact hQ⟩
  let P := fun x => ∫ s in (0:ℝ)..x,A s
  have hP (x : ℝ) : HasDerivAt P (A x) x :=
    intervalIntegral.integral_hasDerivAt_right (hAc.intervalIntegrable _ _)
      hAc.aestronglyMeasurable.stronglyMeasurableAtFilter hAc.continuousAt
  have hPd : deriv P=A := funext fun x => (hP x).deriv
  refine ⟨P,?_,?_⟩
  · change ContDiff ℝ (1+1) P
    rw [contDiff_succ_iff_deriv]
    exact ⟨fun x => (hP x).differentiableAt,by simp,by rw [hPd]; exact hA1⟩
  · intro x
    rw [hPd,hAd]

/-- A continuous weak solution of f''=Q on an interval is exactly a genuine
global C2 function there, with the prescribed actual second derivative.
Use: the target Green columns acquire local classical derivatives from
their proved inverse test identity, with no extra regularity hypotheses.
Article: jacobi, Proposition 2.2.
Source: the one-dimensional weak derivative regularity theorem.
Proof: subtract an actual double primitive of Q. Compact integration by
parts leaves zero weak second derivative, so the difference is affine. -/
theorem weak_second_regular {f Q : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : Continuous f) (hQ : Continuous Q)
    (hw : ∀ g : ℝ → ℝ,ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b →
        (∫ s : ℝ,f s*deriv (deriv g) s)=∫ s : ℝ,Q s*g s) :
    ∃ F : ℝ → ℝ,ContDiff ℝ 2 F ∧ (∀ x,deriv (deriv F) x=Q x) ∧
      EqOn f F (Ioo a b) := by
  obtain ⟨P,hP,hPd⟩ := continuous_second_primitive hQ
  have hz (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
      (hs : tsupport g ⊆ Ioo a b) :
      (∫ s : ℝ,(f s-P s)*deriv (deriv g) s)=0 := by
    have hgd : ContDiff ℝ 1 (deriv g) := (show ContDiff ℝ (1+1) g from hg).deriv'
    have hi1 : Integrable (fun s => f s*deriv (deriv g) s) :=
      (hf.mul (hgd.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hc.deriv.deriv.mul_left
    have hi2 : Integrable (fun s => P s*deriv (deriv g) s) :=
      (hP.continuous.mul (hgd.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hc.deriv.deriv.mul_left
    have hp := compact_test_second_derivative hg hc isOpen_univ (subset_univ _) hP.contDiffOn
    simp_rw [hPd] at hp
    simp_rw [sub_mul]
    rw [integral_sub hi1 hi2,hw g hg hc hs]
    have he : (∫ s : ℝ,P s*deriv (deriv g) s)=∫ s : ℝ,Q s*g s := by
      simpa only [mul_comm] using hp
    rw [he,sub_self]
  obtain ⟨A,B,hAB⟩ := weak_second_zero_affine hab (hf.sub hP.continuous) hz
  refine ⟨fun x => P x+(A*x+B),hP.add (contDiff_const.mul contDiff_id |>.add contDiff_const),?_,?_⟩
  · intro x
    have he : deriv (fun s => P s+(A*s+B))=fun s => deriv P s+A := by
      funext s
      simpa only [Pi.add_def,id_eq,mul_one] using ((hP.differentiable (by norm_num) s).hasDerivAt.add
        (((hasDerivAt_id s).const_mul A).add_const B)).deriv
    rw [he]
    simpa only [deriv_add_const] using hPd x
  · intro x hx
    have h := hAB x hx
    change f x-P x=A*x+B at h
    linarith

end
end jacobi.Analysis
