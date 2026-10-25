import polyak.Numerics.Parametric.Dyadic
import polyak.Numerics.Parametric.Contract

/-!
Article: Appendix B, bounded-denominator weighted parameter continuation.
Use: the executable check proves a unique source-system zero on an entire slab,
with no determinant expansion and no trust in external interval outcomes.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def dyadicCenterImage {n : ℕ} (F : Fin n → Expr) (I : IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : DyadicConfig) : Fin n → IntervalRat :=
  fun i => IntervalRat.sub (IntervalRat.singleton (m i))
    (intervalRatMatVec Y (dyadicCenterResidual F I m cfg) i)

noncomputable section

theorem dyadicCenterImage_mem {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (I : IntervalRat) (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : DyadicConfig) (hok : dyadicResidualSucceeded F I m cfg=true)
    {s : ℝ} (hs : s∈I) (i : Fin n) :
    newton (Y.map fun q => (q : ℝ)) F s (fun j => (m j : ℝ)) i∈
      dyadicCenterImage F I m Y cfg i := by
  apply IntervalRat.mem_sub (IntervalRat.mem_singleton (m i))
  exact mem_interval_sum Finset.univ
    (fun j => (Y i j : ℝ)*system F s (fun k => (m k : ℝ)) j)
    (fun j => IntervalRat.scale (Y i j) (dyadicCenterResidual F I m cfg j))
    (fun j _ => IntervalRat.mem_scale (Y i j) (dyadicCenterResidual_mem F hF I m cfg hok hs j))

end

def dyadicWeightedJacobian {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig) : Matrix (Fin n) (Fin n) IntervalRat :=
  dyadicJacobian (scaledSystem F cert.center cert.radius) I (unitBox n) cfg

def dyadicWeightedCenter {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig) : Fin n → IntervalRat :=
  dyadicCenterImage (scaledSystem F cert.center cert.radius) I
    (normalized cert).center (normalized cert).preconditioner cfg

/-- Every arithmetic/AD operation must succeed; the complete enclosure check is finite. -/
def checkDyadic {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig := {}) : Bool :=
  decide (∀ i, (F i).checkADSupported=true) &&
    dyadicJacobianSucceeded (scaledSystem F cert.center cert.radius) I (unitBox n) cfg &&
    dyadicResidualSucceeded (scaledSystem F cert.center cert.radius) I (normalized cert).center cfg &&
    weightedEnclosureCheck cert (dyadicWeightedJacobian F I cert cfg) (dyadicWeightedCenter F I cert cfg)

noncomputable section

/-- Kernel-facing soundness: every real slab parameter has exactly one true system zero. -/
theorem checkDyadic_sound {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig)
    (hc : checkDyadic F I cert cfg=true) :
    ∀ s∈I, ∃! x, FinBoxMem x (coordinateBox cert.center cert.radius) ∧ system F s x=0 := by
  simp only [checkDyadic,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hF,hJ⟩,hC⟩,hcheck⟩ := hc
  have hF' : ∀ i, ADSupported (F i) := fun i => ((F i).checkADSupported_eq_true_iff).mp (hF i)
  have hscaled : ∀ i, ADSupported (scaledSystem F cert.center cert.radius i) :=
    fun i => substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF' i)
  apply weightedEnclosureCheck_sound F hF' I cert _ _ _ _ hcheck
  · intro s hs x hx i j
    exact dyadicJacobian_mem _ hscaled I (unitBox n) cfg hJ hs hx i j
  · intro s hs i
    exact dyadicCenterImage_mem _ hscaled I (normalized cert).center
      (normalized cert).preconditioner cfg hC hs i

end
end polyak.Numerics.Parametric
