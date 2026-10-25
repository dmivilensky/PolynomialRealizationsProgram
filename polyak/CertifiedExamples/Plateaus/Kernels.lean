import polyak.CertifiedExamples.Plateaus.Root
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Exact kernels and slope moments; equalities at the support are algebraic
consequences of the root equation, rather than interval tests containing zero. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open Matrix
open scoped BigOperators

def normalizeVector {d : ℕ} (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => v i / ∑ j, v j

theorem normalizeVector_sum {d : ℕ} (v : Fin d → ℝ) (h : (∑ j,v j) ≠ 0) :
    (∑ i,normalizeVector v i)=1 := by
  simp only [normalizeVector,← Finset.sum_div]
  exact div_self h

theorem adjugate_column_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (h : M.det=0) (j : Fin d) : M.mulVec (fun i => M.adjugate i j)=0 := by
  funext i
  have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) M.mul_adjugate
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,h,zero_smul,
    Pi.zero_apply,Matrix.zero_apply] using he

theorem adjugate_row_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (h : M.det=0) (j : Fin d) :
    ∀ i, (∑ r, M.adjugate j r*M r i)=0 := by
  intro i
  have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A j i) M.adjugate_mul
  simpa only [Matrix.mul_apply,h,zero_smul,Pi.zero_apply,Matrix.zero_apply] using he

theorem normalizeVector_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (h : M.mulVec v=0) : M.mulVec (normalizeVector v)=0 := by
  funext i
  have he := congrFun h i
  simp only [Matrix.mulVec,dotProduct,Pi.zero_apply] at he ⊢
  simp only [normalizeVector,← mul_div_assoc,← Finset.sum_div,he,zero_div]

theorem normalizeVector_left_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (h : ∀ i,(∑ r,v r*M r i)=0) :
    ∀ i,(∑ r,normalizeVector v r*M r i)=0 := by
  intro i
  simp only [normalizeVector,div_mul_eq_mul_div,← Finset.sum_div,h i,zero_div]

def positivePrimal {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    Fin d → ℝ := normalizeVector (fun i => M.adjugate i j)

def positiveDual {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    Fin d → ℝ := normalizeVector (fun i => M.adjugate j i)

theorem positivePrimal_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (j : Fin d) (h : M.det=0) : M.mulVec (positivePrimal M j)=0 :=
  normalizeVector_kernel M _ (adjugate_column_kernel M h j)

theorem positiveDual_kernel {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (j : Fin d) (h : M.det=0) : ∀ i,(∑ r,positiveDual M j r*M r i)=0 :=
  normalizeVector_left_kernel M _ (adjugate_row_kernel M h j)

def slopeMoments {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (t : Fin d → ℝ) :
    Fin d → ℝ := fun i => (V.adjugate.mulVec t) i / V.det

theorem slopeMoments_solve {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (t : Fin d → ℝ) (h : V.det ≠ 0) : V.mulVec (slopeMoments V t)=t := by
  have he := V.mulVec_cramer t
  rw [Matrix.cramer_eq_adjugate_mulVec] at he
  funext i
  have hi := congrFun he i
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hi ⊢
  simp only [slopeMoments,Matrix.mulVec,dotProduct,← mul_div_assoc,← Finset.sum_div]
  rw [hi]
  exact mul_div_cancel_left₀ _ h

theorem rank_eq_of_kernel_minor {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : Fin (n+1) → ℝ) (hv : M.mulVec v=0) (hne : v≠0)
    (hminor : (M.submatrix Fin.succ Fin.succ).det≠0) : M.rank=n := by
  have hlow : n≤M.rank := by
    have hh := Matrix.rank_submatrix_le M Fin.succ Fin.succ
    rw [Matrix.rank_of_det_ne_zero hminor,Fintype.card_fin] at hh
    exact hh
  have hker : 0<Module.finrank ℝ M.mulVecLin.ker := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v,hv⟩,?_⟩
    intro hz
    exact hne (congrArg Subtype.val hz)
  have hdim := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank+Module.finrank ℝ M.mulVecLin.ker=Module.finrank ℝ (Fin (n+1)→ℝ) at hdim
  rw [Module.finrank_pi,Fintype.card_fin] at hdim
  omega

end polyak.CertifiedExamples.Plateaus
