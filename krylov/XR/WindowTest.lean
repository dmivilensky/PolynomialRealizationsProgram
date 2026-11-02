import krylov.Secant.Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
Article: main_krylov, prop:cert, the actual Hermitian window test.
Use: test the observed latest-information model and its true skew defect,
prove inheritance by every ordered subwindow, and select the longest
admissible suffix by a genuine finite search. The relative-norm equivalence
is proved separately; no window admissibility is an input certificate.
Source: principal-submatrix positivity and the elementary ordered-window
identities; Cholesky realizes the same nested positive-definite test.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped ComplexOrder
variable {p q : ℕ}

/-- The genuine complex Hermitian form tested by the source algorithm.
Article: main_krylov, prop:cert, Tbar+i D/theta_w. -/
def hermitianWindowMatrix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  (latest M).map Complex.ofReal+(Complex.I/(θ : ℂ)) • (defect M).map Complex.ofReal

/-- Actual refutation is the failure of the original Hermitian positivity
test, independent of any externally asserted budget. Article: prop:cert. -/
def windowUnrefuted (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (hermitianWindowMatrix θ M).PosDef

/-- Restricting an ordered observed window commutes with retaining its
latest upper-triangular information. Article: main_krylov, prop:cert. -/
theorem latest_submatrix (M : Matrix (Fin p) (Fin p) ℝ) (f : Fin q → Fin p) (hf : StrictMono f) :
    latest (M.submatrix f f)=(latest M).submatrix f f := by
  ext i j
  simp only [latest,submatrix_apply,hf.monotone.map_min,hf.monotone.map_max]

/-- The actual skew defect restricts exactly to every retained subwindow.
Article: main_krylov, prop:cert. -/
theorem defect_submatrix (M : Matrix (Fin p) (Fin p) ℝ) (f : Fin q → Fin p) :
    defect (M.submatrix f f)=(defect M).submatrix f f := rfl

/-- The Hermitian test on an ordered subset is precisely a principal
submatrix of the original observed test. Article: prop:cert. -/
theorem hermitianWindowMatrix_submatrix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (f : Fin q → Fin p) (hf : StrictMono f) :
    hermitianWindowMatrix θ (M.submatrix f f)=(hermitianWindowMatrix θ M).submatrix f f := by
  simp only [hermitianWindowMatrix,latest_submatrix M f hf,defect_submatrix]
  rfl

/-- Positivity is hereditary for every actual ordered subwindow.
Article: main_krylov, prop:cert. -/
theorem windowUnrefuted_submatrix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (f : Fin q → Fin p) (hf : StrictMono f) (hM : windowUnrefuted θ M) :
    windowUnrefuted θ (M.submatrix f f) := by
  rw [windowUnrefuted,hermitianWindowMatrix_submatrix θ M f hf]
  exact hM.submatrix hf.injective

/-- The real observed suffix starts at the indicated chronological index.
An index beyond the window gives its genuine empty suffix. Article: prop:cert. -/
def windowSuffixIndex (p o : ℕ) (i : Fin (p-o)) : Fin p := ⟨o+i.val,by have hi := i.isLt; omega⟩

/-- Suffix indexing keeps the actual chronological order. Article: prop:cert. -/
theorem windowSuffixIndex_strictMono (p o : ℕ) : StrictMono (windowSuffixIndex p o) := by
  intro i j hij
  change o+i.val<o+j.val
  exact Nat.add_lt_add_left hij o

/-- The actual observed matrix after discarding the oldest o pairs.
Article: main_krylov, prop:cert and alg:xr. -/
def windowSuffix (M : Matrix (Fin p) (Fin p) ℝ) (o : ℕ) : Matrix (Fin (p-o)) (Fin (p-o)) ℝ :=
  M.submatrix (windowSuffixIndex p o) (windowSuffixIndex p o)

/-- An empty window passes the actual positive-definite test vacuously.
Article: main_krylov, prop:cert, empty suffix boundary. -/
theorem windowUnrefuted_empty_suffix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    windowUnrefuted θ (windowSuffix M p) := by
  have he : hermitianWindowMatrix θ (windowSuffix M p)=1 := by
    ext i
    have hi := i.isLt
    omega
  rw [windowUnrefuted,he]
  exact Matrix.PosDef.one

/-- A genuine admissible suffix always exists, so the original finite
selection algorithm is total. Article: main_krylov, prop:cert. -/
theorem exists_unrefuted_suffix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    ∃ o : ℕ,o≤p ∧ windowUnrefuted θ (windowSuffix M o) :=
  ⟨p,le_rfl,windowUnrefuted_empty_suffix θ M⟩

/-- The longest actual admissible suffix: choose the first discarded-prefix
length whose genuine Hermitian test passes. Article: prop:cert and alg:xr. -/
def unrefutedSuffix (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : ℕ := by
  classical
  exact Nat.find (exists_unrefuted_suffix θ M)

/-- The selected suffix is within the observed window and really passes
the original test. Article: main_krylov, prop:cert. -/
theorem unrefutedSuffix_spec (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    unrefutedSuffix θ M≤p ∧ windowUnrefuted θ (windowSuffix M (unrefutedSuffix θ M)) := by
  classical
  exact Nat.find_spec (exists_unrefuted_suffix θ M)

/-- Every longer suffix fails; hence the chosen actual retained suffix is
maximal, not merely one acceptable window. Article: prop:cert. -/
theorem unrefutedSuffix_minimal (θ : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (o : ℕ)
    (ho : o≤p) (hM : windowUnrefuted θ (windowSuffix M o)) : unrefutedSuffix θ M≤o := by
  classical
  exact Nat.find_min' (exists_unrefuted_suffix θ M) ⟨ho,hM⟩

end
end krylov.XR
