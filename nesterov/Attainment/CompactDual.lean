import nesterov.Attainment.ComplexSymbols
import Mathlib.Analysis.Convex.Combination

/-! A single compact convex Banach hull contains normalized certificates at
all exponents in the chosen interval. Both minimizer labels remain distinct. -/
noncomputable section
open Set
open scoped Topology OnePoint
namespace nesterov.Attainment

abbrev DualPoint (lo hi : ℝ) := ℝ × C(LagDomain lo hi,ℂ)
abbrev DualLabel := Bool × OnePoint ℕ

def dualFamily (lo hi : ℝ) (hlo : 0 < lo)
    (G S : C(LagDomain lo hi,ℂ)) (δ : ℝ) : C(OnePoint ℕ,DualPoint lo hi) where
  toFun l := (δ, G*(compactifiedKernels lo hi hlo l).1-
    (2*δ) • (S*(compactifiedKernels lo hi hlo l).2))
  continuous_toFun := by
    have hA := (compactifiedKernels lo hi hlo).continuous.fst
    have hB := (compactifiedKernels lo hi hlo).continuous.snd
    exact continuous_const.prodMk
      ((continuous_const.mul hA).sub ((continuous_const.mul hB).const_smul (2*δ)))

def dualLabelMap (lo hi : ℝ) (hlo : 0 < lo)
    (G S : C(LagDomain lo hi,ℂ)) : C(DualLabel,DualPoint lo hi) where
  toFun l := dualFamily lo hi hlo G S (if l.1 then -1 else 1) l.2
  continuous_toFun := by
    apply continuous_prod_of_discrete_left.mpr
    intro b
    exact (dualFamily lo hi hlo G S (if b then -1 else 1)).continuous

def dualGenerators (lo hi : ℝ) (hlo : 0 < lo) (G S : C(LagDomain lo hi,ℂ)) :
    Set (DualPoint lo hi) := Set.range (dualLabelMap lo hi hlo G S)

def dualHull (lo hi : ℝ) (hlo : 0 < lo) (G S : C(LagDomain lo hi,ℂ)) :
    Set (DualPoint lo hi) := closure (convexHull ℝ (dualGenerators lo hi hlo G S))

theorem isCompact_dualGenerators (lo hi : ℝ) (hlo : 0 < lo) (G S : C(LagDomain lo hi,ℂ)) :
    IsCompact (dualGenerators lo hi hlo G S) :=
  isCompact_range (dualLabelMap lo hi hlo G S).continuous

theorem isCompact_dualHull (lo hi : ℝ) (hlo : 0 < lo) (G S : C(LagDomain lo hi,ℂ)) :
    IsCompact (dualHull lo hi hlo G S) :=
  polyak.Spectral.isCompact_closure_convexHull (isCompact_dualGenerators lo hi hlo G S)

theorem dualHull_le {lo hi : ℝ} {hlo : 0 < lo} {G S : C(LagDomain lo hi,ℂ)}
    (L : DualPoint lo hi →L[ℝ] ℝ) (b : ℝ)
    (h : ∀ d ∈ dualGenerators lo hi hlo G S, L d ≤ b)
    {d : DualPoint lo hi} (hd : d ∈ dualHull lo hi hlo G S) : L d ≤ b := by
  exact (closure_minimal ((convex_halfSpace_le L.toLinearMap.isLinear b).convexHull_subset_iff.mpr h)
    (isClosed_le L.continuous continuous_const)) hd

theorem dualHull_eq {lo hi : ℝ} {hlo : 0 < lo} {G S : C(LagDomain lo hi,ℂ)}
    (L : DualPoint lo hi →L[ℝ] ℝ) (b : ℝ)
    (h : ∀ d ∈ dualGenerators lo hi hlo G S, L d = b)
    {d : DualPoint lo hi} (hd : d ∈ dualHull lo hi hlo G S) : L d = b := by
  exact (closure_minimal ((convex_hyperplane L.toLinearMap.isLinear b).convexHull_subset_iff.mpr h)
    (isClosed_eq L.continuous continuous_const)) hd

theorem sum_mem_dualHull {lo hi : ℝ} {hlo : 0 < lo} {G S : C(LagDomain lo hi,ℂ)}
    {I : Type*} [Fintype I] (w : I → ℝ) (d : I → DualPoint lo hi)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hd : ∀ i, d i ∈ dualGenerators lo hi hlo G S) :
    (∑ i, w i • d i) ∈ dualHull lo hi hlo G S := by
  apply subset_closure
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) hsum
    (fun i _ => subset_convexHull ℝ _ (hd i))

def parameterSlice (lo hi : ℝ) (s : LagParameter lo hi) : C(LagWindow lo,LagDomain lo hi) :=
  ⟨fun z => (s,z), continuous_const.prodMk continuous_id⟩

def restrictSymbolCLM (lo hi : ℝ) (s : LagParameter lo hi) :
    DualPoint lo hi →L[ℝ] C(LagWindow lo,ℂ) :=
  (ContinuousMap.compCLM ℝ ℂ (parameterSlice lo hi s)).comp
    (ContinuousLinearMap.snd ℝ ℝ C(LagDomain lo hi,ℂ))

def traceCLM (lo hi : ℝ) (s : LagParameter lo hi) (z : LagWindow lo) :
    DualPoint lo hi →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousMap.evalCLM ℝ z).comp (restrictSymbolCLM lo hi s))

def imaginaryCLM (lo hi : ℝ) (s : LagParameter lo hi) (z : LagWindow lo) :
    DualPoint lo hi →L[ℝ] ℝ :=
  Complex.imCLM.comp ((ContinuousMap.evalCLM ℝ z).comp (restrictSymbolCLM lo hi s))

end nesterov.Attainment
