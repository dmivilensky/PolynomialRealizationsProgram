import jacobi.Analysis.PointSource
import jacobi.GelfandLevitan.TargetTestDomain
import jacobi.Trichotomy.GreenPositivity

/-!
Article: jacobi, Proposition 2.2.
The genuine target Green column has classical local branches and a unit
source jump. Only compact interior tests are used; singular endpoints never
enter the regularity argument.
Source: compact-test spectral identification and one-dimensional weak regularity.
Use: targetGreen_column_model fixes the actual Wronskian normalization in
the exponential kernel representation of the original packed density.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine target Green column in real coordinates; projection merely
extends its continuous physical representative outside the closed interval.
Use: targetGreen_column_model concerns its true derivatives on (0,1).
Article: jacobi, Proposition 2.2.
-/
def targetGreenColumn (a : ℝ) (ha : -1<a) (t : Interval) (s : ℝ) : ℝ :=
  targetGreenKernel a ha t (projIcc 0 1 (by norm_num) s)

/-- The original real-coordinate Green column is continuous everywhere.
Use: the compact-test weak regularity theorem applies to its unchanged
continuous physical representative, rather than an arbitrary L2 version.
Article: jacobi, Proposition 2.2.
Proof: compose the actual continuous Green row with the continuous projection. -/
theorem targetGreenColumn_continuous (a : ℝ) (ha : -1<a) (t : Interval) :
    Continuous (targetGreenColumn a ha t) :=
  ((targetGreenKernelMap a ha).curry t).continuous.comp continuous_projIcc

/-- The real-coordinate column agrees at every original physical point.
Use: targetGreen_real_test_identity retains the exact article kernel when
passing between subtype integrals and ordinary real integrals.
Article: jacobi, Proposition 2.2.
Proof: the closed-interval projection fixes all points in that interval. -/
theorem targetGreenColumn_eq (a : ℝ) (ha : -1<a) (t s : Interval) :
    targetGreenColumn a ha t s=targetGreenKernel a ha t s := by
  simp only [targetGreenColumn,projIcc_of_mem (by norm_num) s.property]

/-- The original continuous target column satisfies its unit-source test
identity as an ordinary integral on the whole real line.
Use: targetGreen_column_model applies the local weak-to-classical theorem
without changing either the original operator or its spatial kernel.
Article: jacobi, Proposition 2.2.
Proof: the compact differential expression vanishes outside the physical
interval; the actual subtype test identity therefore equals its real integral. -/
theorem targetGreen_real_test_identity (a : ℝ) (ha : -1<a) (t : Interval)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo (0:ℝ) 1) :
    (∫ s : ℝ,testExpression a ha g s*targetGreenColumn a ha t s)=g t := by
  have he := targetGreen_test_identity a ha hg hc hs t
  have hsub : (∫ s : Interval,testExpression a ha g s*targetGreenKernel a ha t s)=
      ∫ s : ℝ,testExpression a ha g s*targetGreenColumn a ha t s := by
    simp_rw [← targetGreenColumn_eq a ha t]
    rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
      (fun s : ℝ => testExpression a ha g s*targetGreenColumn a ha t s)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs'
    have hn : s∉tsupport g := fun h => hs' ⟨(hs h).1.le,(hs h).2.le⟩
    have hn' : s∉tsupport (testExpression a ha g) :=
      fun h => hn (testExpression_tsupport a ha g h)
    simp [image_eq_zero_of_notMem_tsupport hn']
  rw [hsub] at he
  exact he

/-- On each compact interior interval the actual target Green column is
a genuine C2 function minus exactly the positive part at its source.
Use: this supplies both classical homogeneous branches and the derivative
jump -1 which fixes the intrinsic exponential coordinate's scale.
Article: jacobi, Proposition 2.2.
Proof: extend the continuous forcing V*G from the compact interval by
projection. The original compact-test identity is precisely the unit-source
weak equation there. The proved local point-source regularity gives the
actual C2 representative and its true second derivative. -/
theorem targetGreen_column_model (a : ℝ) (ha : -1<a) (t : Interval)
    {l r : ℝ} (hl : 0<l) (hr : r<1) (hlr : l<r) :
    ∃ F : ℝ → ℝ,ContDiff ℝ 2 F ∧
      (∀ s∈Ioo l r,deriv (deriv F) s=targetPotential a ha s*targetGreenColumn a ha t s) ∧
      ∀ s∈Ioo l r,targetGreenColumn a ha t s=F s-max (s-(t:ℝ)) 0 := by
  let p := projIcc l r hlr.le
  let Q := fun s : ℝ => targetPotential a ha (p s)*targetGreenColumn a ha t (p s)
  have hQ : Continuous Q :=
    ((targetPotential_continuousOn a ha).mono (show Icc l r⊆Ioo (0:ℝ) 1 from
      fun s hs => ⟨hl.trans_le hs.1,hs.2.trans_lt hr⟩)).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun s => (p s).property) |>.mul
          ((targetGreenColumn_continuous a ha t).comp (continuous_subtype_val.comp continuous_projIcc))
  have hQe (s : ℝ) (hs : s∈Icc l r) : Q s=targetPotential a ha s*targetGreenColumn a ha t s := by
    simp only [Q,p,projIcc_of_mem hlr.le hs]
  have hw (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
      (hs : tsupport g ⊆ Ioo l r) :
      (∫ s : ℝ,targetGreenColumn a ha t s*deriv (deriv g) s)=
        (∫ s : ℝ,Q s*g s)-g t := by
    have hs0 : tsupport g ⊆ Ioo (0:ℝ) 1 := fun s hs' =>
      ⟨hl.trans (hs hs').1,(hs hs').2.trans hr⟩
    have he := targetGreen_real_test_identity a ha t hg hc hs0
    have hgd : ContDiff ℝ 1 (deriv g) := (show ContDiff ℝ (1+1) g from hg).deriv'
    have hi1 : Integrable (fun s => targetGreenColumn a ha t s*deriv (deriv g) s) :=
      ((targetGreenColumn_continuous a ha t).mul (hgd.continuous_deriv (by norm_num))
        ).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left
    have hi2 : Integrable (fun s => Q s*g s) :=
      (hQ.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
    have heq : (fun s => testExpression a ha g s*targetGreenColumn a ha t s)=
        (fun s => -(targetGreenColumn a ha t s*deriv (deriv g) s)+Q s*g s) := by
      funext s
      by_cases hs' : s∈tsupport g
      · rw [hQe s ⟨(hs hs').1.le,(hs hs').2.le⟩]
        dsimp only [testExpression]
        ring
      · simp [testExpression,image_eq_zero_of_notMem_tsupport hs',mul_comm]
    have hadd := integral_add hi1.neg hi2
    simp only [Pi.neg_apply] at hadd
    rw [heq,hadd,integral_neg] at he
    linarith
  obtain ⟨F,hF,hFd,hFe⟩ := jacobi.Analysis.weak_point_source_regular hlr
    (targetGreenColumn_continuous a ha t) hQ hw
  exact ⟨F,hF,fun s hs => (hFd s).trans (hQe s ⟨hs.1.le,hs.2.le⟩),hFe⟩

end
end jacobi.Trichotomy
