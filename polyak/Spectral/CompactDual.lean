import polyak.Spectral.ComplexLag
import Mathlib.Analysis.Convex.Combination

/-!
Article: Appendix A, the limiting dual symbol on compactified lags.
Use: store the charge and all three polynomial coefficients in u in one fixed
compact convex set, so limits of certificates retain both cancellation and analyticity.
Proof: uniform geometric convergence on the complex window and compactness
of the closed convex hull of a compact subset of a real Banach space.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter
open scoped Topology OnePoint

/-- Article: charge and the three exact coefficients of a quadratic dual symbol in u. -/
abbrev DualCoefficient (s : ℝ) :=
  ℝ × (C(lagWindow s,ℂ) × (C(lagWindow s,ℂ) × C(lagWindow s,ℂ)))

/-- Article: evaluation at the actual twist. Use: parameter variation is finite polynomial algebra. -/
def evaluateDual {s : ℝ} (u : ℝ) (d : DualCoefficient s) : C(lagWindow s,ℂ) :=
  d.2.1+u • d.2.2.1+u^2 • d.2.2.2

/-- Article: joint continuity in the twist and all limiting coefficients. -/
@[fun_prop] theorem continuous_evaluateDual (s : ℝ) :
    Continuous (fun p : ℝ × DualCoefficient s => evaluateDual p.1 p.2) := by
  unfold evaluateDual
  fun_prop

/-- Article: coefficient evaluation is a continuous real linear map. -/
def evaluateDualCLM {s : ℝ} (u : ℝ) : DualCoefficient s →L[ℝ] C(lagWindow s,ℂ) where
  toFun := evaluateDual u
  map_add' d e := by dsimp [evaluateDual]; module
  map_smul' a d := by dsimp [evaluateDual]; module
  cont := (continuous_evaluateDual s).comp (continuous_const.prodMk continuous_id)

/-- Article: the real value of the dual symbol is a continuous linear functional. -/
def dualTraceCLM {s : ℝ} (u : ℝ) (z : lagWindow s) : DualCoefficient s →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousMap.evalCLM ℝ z).comp (evaluateDualCLM u))

/-- Article: normalized lag coefficients on the one-point compactification. -/
def coefficientFamily (s δ : ℝ) (hs : 0 < s) (hδ : |δ| ≤ 1) :
    C(OnePoint ℕ,DualCoefficient s) where
  toFun l :=
    let F0 := compactifiedLagMap 0 s δ hs hδ l
    let F1 := compactifiedLagMap 1 s δ hs hδ l
    let Fm := compactifiedLagMap (-1) s δ hs hδ l
    (δ,(F0,((1/2 : ℝ) • (F1-Fm),(1/2 : ℝ) • (F1+Fm)-F0)))
  continuous_toFun := by
    dsimp
    exact continuous_const.prodMk
      ((compactifiedLagMap 0 s δ hs hδ).continuous.prodMk
        (((compactifiedLagMap 1 s δ hs hδ).continuous.sub
          (compactifiedLagMap (-1) s δ hs hδ).continuous).const_smul (1/2 : ℝ) |>.prodMk
            ((((compactifiedLagMap 1 s δ hs hδ).continuous.add
              (compactifiedLagMap (-1) s δ hs hδ).continuous).const_smul (1/2 : ℝ)).sub
                (compactifiedLagMap 0 s δ hs hδ).continuous)))

/-- Article: the two compactified families, including both minimizer constraints. -/
def dualGenerators (s : ℝ) (hs : 0 < s) : Set (DualCoefficient s) :=
  range (coefficientFamily s 1 hs (by norm_num)) ∪
    range (coefficientFamily s (-1) hs (by norm_num))

/-- Article: the compact convex set of all normalized limiting dual combinations. -/
def dualHull (s : ℝ) (hs : 0 < s) : Set (DualCoefficient s) :=
  closure (convexHull ℝ (dualGenerators s hs))

/-- Article: the generator set is compact, with two genuine lag-at-infinity points. -/
theorem isCompact_dualGenerators (s : ℝ) (hs : 0 < s) : IsCompact (dualGenerators s hs) :=
  (isCompact_range (coefficientFamily s 1 hs (by norm_num)).continuous).union
    (isCompact_range (coefficientFamily s (-1) hs (by norm_num)).continuous)

/-- Article: compactness of every normalized certificate, uniformly over its lag support. -/
theorem isCompact_dualHull (s : ℝ) (hs : 0 < s) : IsCompact (dualHull s hs) :=
  isCompact_closure_convexHull (isCompact_dualGenerators s hs)

/-- Article: every closed linear inequality on the compactified generators survives the dual limit. -/
theorem dualHull_le {s : ℝ} {hs : 0 < s} (L : DualCoefficient s →L[ℝ] ℝ) (b : ℝ)
    (h : ∀ d ∈ dualGenerators s hs, L d ≤ b) {d : DualCoefficient s} (hd : d ∈ dualHull s hs) :
    L d ≤ b := by
  exact (closure_minimal ((convex_halfSpace_le L.toLinearMap.isLinear b).convexHull_subset_iff.mpr h)
    (isClosed_le L.continuous continuous_const)) hd

/-- Article: exact linear identities also survive the limiting certificate construction. -/
theorem dualHull_eq {s : ℝ} {hs : 0 < s} (L : DualCoefficient s →L[ℝ] ℝ) (b : ℝ)
    (h : ∀ d ∈ dualGenerators s hs, L d = b) {d : DualCoefficient s} (hd : d ∈ dualHull s hs) :
    L d = b := by
  exact (closure_minimal ((convex_hyperplane L.toLinearMap.isLinear b).convexHull_subset_iff.mpr h)
    (isClosed_eq L.continuous continuous_const)) hd

/-- Article: normalized certificate combinations belong to the fixed compact hull. -/
theorem sum_mem_dualHull {s : ℝ} {hs : 0 < s} {I : Type*} [Fintype I]
    (w : I → ℝ) (d : I → DualCoefficient s) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i,w i=1) (hd : ∀ i,d i ∈ dualGenerators s hs) :
    (∑ i,w i • d i) ∈ dualHull s hs := by
  apply subset_closure
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) hsum
    (fun i _ => subset_convexHull ℝ _ (hd i))

/-- Article: exact polynomial dependence of every finite normalized lag on the twist. -/
theorem complexLag_quadratic (u s δ : ℝ) (n : ℕ) (z : ℂ) :
    complexLag u s δ n z = complexLag 0 s δ n z+
      (u : ℂ)*((complexLag 1 s δ n z-complexLag (-1) s δ n z)/2)+
      (u : ℂ)^2*((complexLag 1 s δ n z+complexLag (-1) s δ n z)/2-complexLag 0 s δ n z) := by
  unfold complexLag complexGap
  push_cast
  ring

/-- Article: coefficient evaluation recovers the actual finite normalized symbol. -/
theorem evaluateDual_coefficient_coe (u s δ : ℝ) (hs : 0 < s) (hδ : |δ| ≤ 1) (n : ℕ) :
    evaluateDual u (coefficientFamily s δ hs hδ (n : OnePoint ℕ)) = complexLagMap u s δ n := by
  ext z
  change complexLag 0 s δ n z+(u • ((1/2 : ℝ) •
      (complexLag 1 s δ n z-complexLag (-1) s δ n z)))+
      u^2 • ((1/2 : ℝ) • (complexLag 1 s δ n z+complexLag (-1) s δ n z)-complexLag 0 s δ n z) =
        complexLag u s δ n z
  rw [complexLag_quadratic u s δ n z]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
    Complex.ofReal_pow]
  ring

/-- Article: the infinite-lag coefficients recover the actual minimizer gap. -/
theorem evaluateDual_coefficient_infty (u s δ : ℝ) (hs : 0 < s) (hδ : |δ| ≤ 1) :
    evaluateDual u (coefficientFamily s δ hs hδ ∞) = complexGapMap u s := by
  ext z
  change complexGap 0 z+u • ((1/2 : ℝ) • (complexGap 1 z-complexGap (-1) z))+
    u^2 • ((1/2 : ℝ) • (complexGap 1 z+complexGap (-1) z)-complexGap 0 z) = complexGap u z
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
    Complex.ofReal_pow]
  unfold complexGap
  push_cast
  ring

end
end polyak.Spectral
