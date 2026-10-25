import polyak.Growth.HorizonWindow
import polyak.Growth.HorizonExtension
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
Article: Appendix C, the closed convex cone of finite Gram windows.
Use: all recurrence gradients are reconstructed linearly from window positions;
the interpolation constraints are genuine continuous linear functionals of the
Gram matrix and relative values. Positive semidefiniteness encodes symmetry.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section
open Matrix
open scoped MatrixOrder

abbrev WindowMatrix (H : ℕ) := Matrix (Fin (H+2)) (Fin (H+2)) ℝ

/-- Article: the ambient finite-dimensional Gram-and-value space. -/
abbrev WindowSpace (H : ℕ) := WindowMatrix H × (Fin H → ℝ)

/-- Article: the position e_{i+1} in a window e₀,…,e_{H+1}. -/
def positionCoefficient {H : ℕ} (i : Fin H) : Fin (H+2) → ℝ :=
  Pi.single i.castSucc.succ 1

/-- Article: recurrence reconstruction σ_{i+1}=(e_{i+2}−Ae_{i+1}+βe_i)/B. -/
def gradientCoefficient {H : ℕ} (A B β : ℝ) (i : Fin H) : Fin (H+2) → ℝ :=
  (1/B) • (Pi.single i.succ.succ 1-A • positionCoefficient i+
    β • Pi.single i.castSucc.castSucc 1)

/-- Article: the Gram pairing of two fixed position combinations is a continuous linear map. -/
def gramPair {H : ℕ} (a b : Fin (H+2) → ℝ) : WindowSpace H →L[ℝ] ℝ :=
  ∑ i,∑ j,(a i*b j) •
    ((ContinuousLinearMap.proj j : (Fin (H+2) → ℝ) →L[ℝ] ℝ) ∘L
      (ContinuousLinearMap.proj i : WindowMatrix H →L[ℝ] (Fin (H+2) → ℝ)) ∘L
      ContinuousLinearMap.fst ℝ (WindowMatrix H) (Fin H → ℝ))

theorem gramPair_apply {H : ℕ} (a b : Fin (H+2) → ℝ) (Y : WindowSpace H) :
    gramPair a b Y=∑ i,∑ j,a i*b j*Y.1 i j := by
  simp [gramPair,ContinuousLinearMap.comp_apply]
  rfl

def valueCoordinate {H : ℕ} (i : Fin H) : WindowSpace H →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : (Fin H → ℝ) →L[ℝ] ℝ) ∘L
    ContinuousLinearMap.snd ℝ (WindowMatrix H) (Fin H → ℝ)

/-- Article: the actual star interpolation residual, linear in the Gram data. -/
def starT {H : ℕ} (A B β : ℝ) (i : Fin H) : WindowSpace H →L[ℝ] ℝ :=
  valueCoordinate i-(1/2 : ℝ) • gramPair (gradientCoefficient A B β i) (positionCoefficient i)

def starR {H : ℕ} (A B β : ℝ) (i : Fin H) : WindowSpace H →L[ℝ] ℝ :=
  (1/4 : ℝ) • (gramPair (positionCoefficient i) (positionCoefficient i)-
    gramPair (gradientCoefficient A B β i) (gradientCoefficient A B β i))

/-- Article: every pair residual has the exact same finite Gram interpretation. -/
def pairT {H : ℕ} (A B β : ℝ) (i j : Fin H) : WindowSpace H →L[ℝ] ℝ :=
  valueCoordinate j-valueCoordinate i-(1/2 : ℝ) •
    gramPair (gradientCoefficient A B β i+gradientCoefficient A B β j)
      (positionCoefficient j-positionCoefficient i)

def pairR {H : ℕ} (A B β : ℝ) (i j : Fin H) : WindowSpace H →L[ℝ] ℝ :=
  (1/4 : ℝ) • (gramPair (positionCoefficient j-positionCoefficient i)
      (positionCoefficient j-positionCoefficient i)-
    gramPair (gradientCoefficient A B β j-gradientCoefficient A B β i)
      (gradientCoefficient A B β j-gradientCoefficient A B β i))

/-- Article: K_H, the finite Gram cone; no closedness or convexity is assumed. -/
def windowCone (A B β : ℝ) (H : ℕ) : Set (WindowSpace H) :=
  {Y | Y.1.PosSemidef ∧
    (∀ i : Fin H,|starT A B β i Y| ≤ starR A B β i Y) ∧
    ∀ i j : Fin H,|pairT A B β i j Y| ≤ pairR A B β i j Y}

/-- Article: K_H is closed because its defining Gram and interpolation conditions are closed. -/
theorem windowCone_isClosed (A B β : ℝ) (H : ℕ) : IsClosed (windowCone A B β H) := by
  have hG : IsClosed {Y : WindowSpace H | Y.1.PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage continuous_fst
  have hs : IsClosed {Y : WindowSpace H | ∀ i : Fin H,|starT A B β i Y| ≤ starR A B β i Y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (starT A B β i).continuous.abs (starR A B β i).continuous)
  have hp : IsClosed {Y : WindowSpace H | ∀ i j : Fin H,|pairT A B β i j Y| ≤ pairR A B β i j Y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_le (pairT A B β i j).continuous.abs (pairR A B β i j).continuous))
  exact hG.inter (hs.inter hp)

theorem windowCone_zero (A B β : ℝ) (H : ℕ) : (0 : WindowSpace H)∈windowCone A B β H := by
  refine ⟨Matrix.PosSemidef.zero,?_,?_⟩ <;> intros <;> simp

theorem windowCone_add {A B β : ℝ} {H : ℕ} {Y Z : WindowSpace H}
    (hY : Y∈windowCone A B β H) (hZ : Z∈windowCone A B β H) : Y+Z∈windowCone A B β H := by
  refine ⟨hY.1.add hZ.1,?_,?_⟩
  · intro i
    rw [map_add,map_add]
    exact (abs_add_le _ _).trans (add_le_add (hY.2.1 i) (hZ.2.1 i))
  · intro i j
    rw [map_add,map_add]
    exact (abs_add_le _ _).trans (add_le_add (hY.2.2 i j) (hZ.2.2 i j))

theorem windowCone_smul {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) {a : ℝ} (ha : 0 ≤ a) : a • Y∈windowCone A B β H := by
  refine ⟨hY.1.smul ha,?_,?_⟩
  · intro i
    simpa only [map_smul,smul_eq_mul,abs_mul,abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (hY.2.1 i) ha
  · intro i j
    simpa only [map_smul,smul_eq_mul,abs_mul,abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (hY.2.2 i j) ha

/-- Article: the Gram constraints define a convex cone in the actual finite-dimensional space. -/
theorem windowCone_convex (A B β : ℝ) (H : ℕ) : Convex ℝ (windowCone A B β H) := by
  intro Y hY Z hZ a b ha hb _
  exact windowCone_add (windowCone_smul hY ha) (windowCone_smul hZ hb)

/-- Article: every positive semidefinite real matrix is the Gram matrix of actual Euclidean vectors. -/
theorem exists_gram_vectors {H : ℕ} {G : WindowMatrix H} (hG : G.PosSemidef) :
    ∃ x : Fin (H+2) → EuclideanSpace ℝ (Fin (H+2)),Matrix.gram ℝ x=G := by
  let C := CFC.sqrt G
  have hC : Cᴴ=C := (CFC.sqrt_nonneg G).posSemidef.isHermitian
  have hCC : Cᴴ*C=G := by
    rw [hC,← sq]
    exact CFC.sq_sqrt G hG.nonneg
  let x : Fin (H+2) → EuclideanSpace ℝ (Fin (H+2)) := fun i => WithLp.toLp 2 (fun j => C j i)
  refine ⟨x,?_⟩
  ext i j
  have hh := congrArg (fun M : WindowMatrix H => M i j) hCC
  simpa only [Matrix.gram_apply,x,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,mul_comm] using hh

end
end polyak.Growth.FiniteHorizon
