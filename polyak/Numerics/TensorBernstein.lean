import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
Article: Appendix B, uniform polynomial signs on rectangular parameter domains.
Use: exact tensor Bernstein annotations certify an independently specified polynomial.
The coefficients include the positive binomial factors; no transformation oracle is trusted.
-/
noncomputable section
namespace polyak.Numerics.TensorBernstein
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 2) ℚ

structure Certificate where
  degree0 : ℕ
  degree1 : ℕ
  coefficient : Fin (degree0+1) → Fin (degree1+1) → ℚ

def Certificate.check (c : Certificate) : Bool :=
  decide (∀ i j, 0<c.coefficient i j)

def basis (d i : ℕ) (x : ℝ) : ℝ := x^i*(1-x)^(d-i)

def Certificate.value (c : Certificate) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, (c.coefficient i j : ℝ)*basis c.degree0 i x*basis c.degree1 j y

def Certificate.polynomial (c : Certificate) : Poly :=
  ∑ i, ∑ j, C (c.coefficient i j)*X 0^(i : ℕ)*(1-X 0)^(c.degree0-i)*
    X 1^(j : ℕ)*(1-X 1)^(c.degree1-j)

theorem basis_nonneg {x : ℝ} (hx : x∈Set.Icc 0 1) (d i : ℕ) :
    0≤basis d i x := mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem exists_basis_pos {x : ℝ} (hx : x∈Set.Icc 0 1) (d : ℕ) :
    ∃ i : Fin (d+1), 0<basis d i x := by
  by_cases h : x=1
  · refine ⟨⟨d,by omega⟩,?_⟩
    simp [basis,h]
  · refine ⟨0,?_⟩
    simp only [basis,Fin.val_zero,pow_zero,one_mul,Nat.sub_zero]
    exact pow_pos (sub_pos.mpr (lt_of_le_of_ne hx.2 h)) _

theorem Certificate.value_pos {c : Certificate} (hc : c.check=true) {x y : ℝ}
    (hx : x∈Set.Icc 0 1) (hy : y∈Set.Icc 0 1) : 0<c.value x y := by
  have hp : ∀ i j, 0<(c.coefficient i j : ℝ) := by
    intro i j
    exact_mod_cast (of_decide_eq_true hc : ∀ i j, 0<c.coefficient i j) i j
  obtain ⟨i,hi⟩ := exists_basis_pos hx c.degree0
  obtain ⟨j,hj⟩ := exists_basis_pos hy c.degree1
  unfold Certificate.value
  apply Finset.sum_pos'
  · intro k _
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hp k l).le (basis_nonneg hx _ _)) (basis_nonneg hy _ _)
  · refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (mul_nonneg (hp i l).le (basis_nonneg hx _ _)) (basis_nonneg hy _ _)
    · exact ⟨j,Finset.mem_univ _,mul_pos (mul_pos (hp i j) hi) hj⟩

theorem Certificate.eval_polynomial (c : Certificate) (x y : ℝ) :
    eval₂Hom (Rat.castHom ℝ) ![x,y] c.polynomial=c.value x y := by
  simp only [Certificate.polynomial,Certificate.value,basis,map_sum,map_mul,map_pow,
    eval₂Hom_C,eval₂Hom_X',map_sub,map_one,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Rat.coe_castHom]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A finite exact polynomial identity and positive coefficients prove a uniform strict sign. -/
theorem Certificate.positive {c : Certificate} {p : Poly} (he : p=c.polynomial)
    (hc : c.check=true) {x y : ℝ} (hx : x∈Set.Icc 0 1) (hy : y∈Set.Icc 0 1) :
    0<eval₂Hom (Rat.castHom ℝ) ![x,y] p := by
  rw [he,c.eval_polynomial]
  exact c.value_pos hc hx hy

end polyak.Numerics.TensorBernstein
