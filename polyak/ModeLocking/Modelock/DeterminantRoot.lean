import polyak.ModeLocking.Gradient.Continuation
import polyak.ModeLocking.Continuation.AdjugateShift

/-! The actual determinant has a unique nearby shift root. Its analytic
implicit root agrees with the positive primal continuation already constructed. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels

def shiftSourcePoint (z : Parameters × ℝ) : SourcePoint :=
  ![z.1 0, z.1 1, z.1 2, z.2]

theorem analyticAt_shiftSourcePoint (z : Parameters × ℝ) :
    AnalyticAt ℝ shiftSourcePoint z := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((ContinuousLinearMap.proj (R := ℝ) 0 : Parameters →L[ℝ] ℝ).analyticAt z.1).comp analyticAt_fst
  · exact ((ContinuousLinearMap.proj (R := ℝ) 1 : Parameters →L[ℝ] ℝ).analyticAt z.1).comp analyticAt_fst
  · exact ((ContinuousLinearMap.proj (R := ℝ) 2 : Parameters →L[ℝ] ℝ).analyticAt z.1).comp analyticAt_fst
  · exact analyticAt_snd

end polyak.ModeLocking.Continuation
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Continuation Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

theorem raw_determinant_zero : ∀ᶠ p in 𝓝 (parameters q),
    tightDeterminant D.reps D.atoms (Gradient.continuedPoint C.shift p) = 0 := by
  filter_upwards [C.equations] with p hp
  let M := D.continuedMatrix C.primalShift p
  have hv : C.primal p ≠ 0 := by
    intro hz
    have hs : (∑ i, C.primal p i) = 1 := hp.2.2.1
    rw [hz] at hs
    simp only [Pi.zero_apply, Finset.sum_const_zero, zero_ne_one] at hs
  change M.det = 0
  by_contra hn
  apply hv
  apply Matrix.mulVec_injective_of_det_ne_zero hn
  exact hp.1.trans (Matrix.mulVec_zero M).symm

/-- The implicit determinant root is uniquely the constructed shift; this
is a local equivalence in the original three parameters and the shift. -/
theorem determinant_root_unique : ∀ᶠ z : Parameters × ℝ in 𝓝 (parameters q, s),
    tightDeterminant D.reps D.atoms (shiftSourcePoint z) = 0 ↔ C.shift z.1 = z.2 := by
  let u : Parameters × ℝ := (parameters q, s)
  let F : Parameters × ℝ → ℝ := fun z => tightDeterminant D.reps D.atoms (shiftSourcePoint z)
  have hout : AnalyticAt ℝ (tightDeterminant D.reps D.atoms) (shiftSourcePoint u) :=
    analyticAt_tightDeterminant q s D.reps D.atoms
  have hF : AnalyticAt ℝ F u :=
    hout.comp (f := shiftSourcePoint) (analyticAt_shiftSourcePoint u)
  let part : ℝ →L[ℝ] ℝ := fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ Parameters ℝ
  have hin : HasFDerivAt (fun t : ℝ => (parameters q, t))
      (ContinuousLinearMap.inr ℝ Parameters ℝ) s :=
    (hasFDerivAt_const (parameters q) s).prodMk (hasFDerivAt_id s)
  have hpart : HasDerivAt (fun t : ℝ => F (parameters q, t)) (part 1) s :=
    (hF.differentiableAt.hasFDerivAt.comp s hin).hasDerivAt
  have hne : part 1 ≠ 0 := by
    rw [← hpart.deriv]
    exact D.tightDeterminant_shift_ne_zero
  obtain ⟨g, hg, hbase, _, hiff⟩ :=
    analytic_implicit_function_unique hF (Gradient.scalar_isInvertible hne)
  have hzero : F u = 0 := D.tightDeterminant_zero
  have hshift : C.shift (parameters q) = s := congrArg Prod.fst C.primalShift_base
  have hgraph : Tendsto (fun p => (p, C.shift p)) (𝓝 (parameters q)) (𝓝 u) := by
    have hc : ContinuousAt C.shift (parameters q) :=
      (analyticAt_fst.comp C.analytic_primalShift).continuousAt
    have hh := (continuousAt_id.prodMk hc).tendsto
    simpa only [id_eq, hshift] using hh
  have hgeq : ∀ᶠ p in 𝓝 (parameters q), g p = C.shift p := by
    filter_upwards [hgraph.eventually hiff, C.raw_determinant_zero] with p hp hd
    exact hp.mp (hd.trans hzero.symm)
  have hfstlim : Tendsto (Prod.fst : Parameters × ℝ → Parameters) (𝓝 u) (𝓝 (parameters q)) :=
    continuous_fst.tendsto u
  have hfst : ∀ᶠ z : Parameters × ℝ in 𝓝 u, g z.1 = C.shift z.1 :=
    hfstlim.eventually hgeq
  filter_upwards [hiff, hfst] with z hz he
  change F z = 0 ↔ C.shift z.1 = z.2
  rw [← he, ← hzero]
  exact hz

end polyak.ModeLocking.RegularData.ContinuationData
