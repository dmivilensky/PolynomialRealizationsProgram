import krylov.XR.WindowTest
import krylov.LinearAlgebra.LeastGain

/-!
Article: main_krylov, prop:cert, the real quadratic form of the Hermitian test.
Use: express the actual complex test in real and imaginary coordinates,
without postulating a spectral decomposition of a skew matrix.
Source: elementary complexification of real finite-dimensional forms.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant
open scoped ComplexOrder BigOperators
variable {p : ℕ}

/-- A genuine complex vector formed from two real coordinate vectors.
Article: main_krylov, prop:cert. -/
def complexVector (x y : Fin p → ℝ) : Fin p → ℂ := fun i=>(x i : ℂ)+Complex.I*(y i : ℂ)

/-- Real matrix action commutes with the true complex scalar embedding.
Article: main_krylov, prop:cert. -/
theorem ofReal_mulVec (A : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) :
    A.map Complex.ofReal *ᵥ (fun i=>(x i : ℂ))=fun i=>((A*ᵥ x) i : ℂ) := by
  ext i
  simp only [mulVec,dotProduct,map_apply,Complex.ofReal_sum,Complex.ofReal_mul]

/-- Real coordinate dot products are preserved by complexification.
Article: main_krylov, prop:cert. -/
theorem ofReal_dotProduct (x y : Fin p → ℝ) :
    (fun i=>(x i : ℂ)) ⬝ᵥ (fun i=>(y i : ℂ))=(x ⬝ᵥ y : ℝ) := by
  simp only [dotProduct,Complex.ofReal_sum,Complex.ofReal_mul]

/-- The real and imaginary actions of an actual complexified pair of real
matrices. Article: main_krylov, prop:cert. -/
theorem complexVector_mulVec (A B : Matrix (Fin p) (Fin p) ℝ) (x y : Fin p → ℝ) :
    (A.map Complex.ofReal+Complex.I • B.map Complex.ofReal)*ᵥ complexVector x y=
      complexVector (A*ᵥ x-B*ᵥ y) (A*ᵥ y+B*ᵥ x) := by
  have he : complexVector x y=(fun i=>(x i : ℂ))+Complex.I • (fun i=>(y i : ℂ)) := rfl
  rw [he]
  simp only [add_mulVec,mulVec_add,smul_mulVec,mulVec_smul,ofReal_mulVec]
  ext i
  simp only [complexVector,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Complex.ofReal_sub,
    Complex.ofReal_add]
  have hi : Complex.I*Complex.I=(-1 : ℂ) := Complex.I_mul_I
  linear_combination ((B*ᵥ y) i : ℂ)*hi

/-- The actual complex inner product has the printed real-coordinate form.
Article: main_krylov, prop:cert. -/
theorem complexVector_dot_re (x y a b : Fin p → ℝ) :
    (star (complexVector x y) ⬝ᵥ complexVector a b).re=x ⬝ᵥ a+y ⬝ᵥ b := by
  change Complex.reCLM (∑ i,star (complexVector x y) i*complexVector a b i)=_
  rw [map_sum]
  simp only [dotProduct,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [complexVector,Complex.mul_re,Complex.mul_im]

/-- The real quadratic form tested by a complex Hermitian matrix is
exactly its real block form. Article: main_krylov, prop:cert. -/
theorem hermitian_pair_quadratic_re (A B : Matrix (Fin p) (Fin p) ℝ) (x y : Fin p → ℝ) :
    (star (complexVector x y) ⬝ᵥ
      ((A.map Complex.ofReal+Complex.I • B.map Complex.ofReal)*ᵥ complexVector x y)).re=
      x ⬝ᵥ (A*ᵥ x)+y ⬝ᵥ (A*ᵥ y)+y ⬝ᵥ (B*ᵥ x)-x ⬝ᵥ (B*ᵥ y) := by
  rw [complexVector_mulVec,complexVector_dot_re,dotProduct_sub,dotProduct_add]
  ring

/-- A real skew form has opposite cross pairings. Article: prop:cert. -/
theorem skew_cross_pairing (K : Matrix (Fin p) (Fin p) ℝ) (hK : Kᵀ= -K) (x y : Fin p → ℝ) :
    y ⬝ᵥ (K*ᵥ x)= -(x ⬝ᵥ (K*ᵥ y)) := by
  rw [dotProduct_mulVec,←mulVec_transpose,hK,neg_mulVec,neg_dotProduct,dotProduct_comm]

end
end krylov.XR
