import krylov.LinearAlgebra.Schur
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, Gram-constrained spectral extension.
Use: reconstruct a physical symmetric matrix from its feasible compression
instead of assuming that positive compressed endpoint tests have an extension.
Source: finite-dimensional positive extension by the orthogonal projection
onto the actual column space; all matrix identities are proved here.
-/

namespace krylov.Completion
noncomputable section
open Matrix
open scoped MatrixOrder
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The true orthogonal column-space projection in a nonorthogonal frame.
Use: the spectral extension must also control the unobserved perpendicular space.
Article: main_krylov, thm:radau.
Proof: the inverse Gram corrects the coordinates of the physical columns. -/
def columnProjection (Z : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  Z*(Zᵀ*Z)⁻¹*Zᵀ

/-- The complement of the actual full-rank column projection is positive semidefinite.
Use: fill the unobserved perpendicular space with the lower spectral endpoint.
Article: main_krylov, thm:radau.
Proof: prove symmetry and idempotence from the actual positive Gram, then
write the complement as its own transpose-square. -/
theorem column_projection_complement (Z : Matrix ι κ ℝ)
    (hG : (Zᵀ*Z).PosDef) : (1-columnProjection Z).PosSemidef := by
  let G := Zᵀ*Z
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hsym : (columnProjection Z).IsSymm := by
    dsimp only [columnProjection]
    rw [Matrix.IsSymm,transpose_mul,transpose_mul,transpose_transpose,hG.1.isSymm.inv.eq]
    simp only [Matrix.mul_assoc]
  have hid : columnProjection Z*columnProjection Z=columnProjection Z := by
    calc
      _=Z*(G⁻¹*G)*G⁻¹*Zᵀ := by simp only [columnProjection,G,Matrix.mul_assoc]
      _=columnProjection Z := by rw [nonsing_inv_mul _ hd,Matrix.mul_one];rfl
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1-columnProjection Z)
  have he : (1-columnProjection Z)ᵀ*(1-columnProjection Z)=1-columnProjection Z := by
    rw [transpose_sub,transpose_one,hsym.eq]
    noncomm_ring [hid]
  simpa only [conjTranspose_eq_transpose_of_trivial,he] using hp

omit [DecidableEq ι] in
/-- The column projection fixes the genuine physical frame.
Use: the extension preserves the entire prescribed compressed matrix.
Article: main_krylov, thm:radau.
Proof: cancel the independently proved invertible Gram on its actual domain. -/
theorem column_projection_frame (Z : Matrix ι κ ℝ)
    (hG : (Zᵀ*Z).PosDef) : columnProjection Z*Z=Z := by
  have hd : IsUnit (Zᵀ*Z).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  calc
    _=Z*((Zᵀ*Z)⁻¹*(Zᵀ*Z)) := by simp only [columnProjection,Matrix.mul_assoc]
    _=Z := by rw [nonsing_inv_mul _ hd,Matrix.mul_one]

/-- Explicit extension of a prescribed compressed form to the physical space.
Use: endpoint curvature completions are actual matrices, including singular
shifted endpoint blocks.
Article: main_krylov, thm:radau.
Proof: lift the compressed form by the inverse Gram and fill its orthogonal
complement with the lower endpoint. -/
def spectralExtension (Z : Matrix ι κ ℝ)
    (T : Matrix κ κ ℝ) (mu : ℝ) : Matrix ι ι ℝ :=
  Z*(Zᵀ*Z)⁻¹*T*(Zᵀ*Z)⁻¹*Zᵀ+mu • (1-columnProjection Z)

/-- The constructed physical extension has exactly the prescribed compression.
Use: no realizability field or assumed endpoint witness is needed.
Article: main_krylov, thm:radau.
Proof: both inverse Grams cancel; the perpendicular fill compresses to zero. -/
theorem spectral_extension_compression (Z : Matrix ι κ ℝ)
    (hG : (Zᵀ*Z).PosDef) (T : Matrix κ κ ℝ) (mu : ℝ) :
    Zᵀ*spectralExtension Z T mu*Z=T := by
  let G := Zᵀ*Z
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hperp : Zᵀ*(1-columnProjection Z)*Z=0 := by
    rw [Matrix.mul_assoc,Matrix.sub_mul,Matrix.one_mul,column_projection_frame Z hG,sub_self,Matrix.mul_zero]
  have he : Zᵀ*spectralExtension Z T mu*Z=
      G*G⁻¹*T*(G⁻¹*G)+mu • (Zᵀ*(1-columnProjection Z)*Z) := by
    simp only [spectralExtension,G,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_assoc]
  rw [he,hperp,smul_zero,add_zero,mul_nonsing_inv _ hd,nonsing_inv_mul _ hd,
    Matrix.one_mul,Matrix.mul_one]

/-- Spectral feasibility of an arbitrary compressed form is equivalent to the
existence of an actual physical symmetric extension in the same closed band.
Use: supply the physical endpoint completions needed by the Radau theorem.
Article: main_krylov, thm:radau.
Proof: compress the two physical shifted positive forms for necessity. For
sufficiency use the explicit inverse-Gram lift, whose lower shift is a positive
congruence and whose upper shift adds a nonnegative perpendicular fill. -/
theorem spectral_extension_iff (Z : Matrix ι κ ℝ)
    (hG : (Zᵀ*Z).PosDef) (T : Matrix κ κ ℝ) (mu L : ℝ) (hmuL : mu≤L) :
    (T-mu • (Zᵀ*Z)).PosSemidef ∧ (L • (Zᵀ*Z)-T).PosSemidef ↔
      ∃ A : Matrix ι ι ℝ,
        (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧ Zᵀ*A*Z=T := by
  constructor
  · rintro ⟨hlo,hhi⟩
    let G := Zᵀ*Z
    let C := G⁻¹*Zᵀ
    let A := spectralExtension Z T mu
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
    have hGi : G⁻¹ᵀ=G⁻¹ := hG.1.isSymm.inv.eq
    have hCsym : Cᵀ=Z*G⁻¹ := by
      simp only [C,transpose_mul,transpose_transpose,hGi]
    have hc : Z*G⁻¹*G*G⁻¹*Zᵀ=columnProjection Z := by
      rw [Matrix.mul_assoc Z G⁻¹ G,nonsing_inv_mul _ hd,Matrix.mul_one]
      rfl
    have hlow : A-mu • 1=Cᵀ*(T-mu • G)*C := by
      rw [hCsym]
      change Z*G⁻¹*T*G⁻¹*Zᵀ+mu • (1-columnProjection Z)-mu • 1=
        Z*G⁻¹*(T-mu • G)*(G⁻¹*Zᵀ)
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
        ← Matrix.mul_assoc,hc]
      module
    have hhigh : L • 1-A=Cᵀ*(L • G-T)*C+(L-mu) • (1-columnProjection Z) := by
      rw [hCsym]
      change L • 1-(Z*G⁻¹*T*G⁻¹*Zᵀ+mu • (1-columnProjection Z))=
        Z*G⁻¹*(L • G-T)*(G⁻¹*Zᵀ)+(L-mu) • (1-columnProjection Z)
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
        ← Matrix.mul_assoc,hc]
      module
    refine ⟨A,?_,?_,spectral_extension_compression Z hG T mu⟩
    · rw [hlow]
      simpa only [conjTranspose_eq_transpose_of_trivial] using hlo.conjTranspose_mul_mul_same C
    · rw [hhigh]
      have hp : (Cᵀ*(L • G-T)*C).PosSemidef := by
        simpa only [conjTranspose_eq_transpose_of_trivial] using hhi.conjTranspose_mul_mul_same C
      exact hp.add ((column_projection_complement Z hG).smul (sub_nonneg.mpr hmuL))
  · rintro ⟨A,hlo,hhi,hcomp⟩
    have hl := hlo.conjTranspose_mul_mul_same Z
    have hh := hhi.conjTranspose_mul_mul_same Z
    simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hcomp] using And.intro hl hh

end
end krylov.Completion
