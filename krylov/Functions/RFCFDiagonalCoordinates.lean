import krylov.Functions.NativeRFCFScaling

/-!
Article: main_krylov, prop:Fcycle, exact scalar-diagonal coordinate estimates.
Use: retain the actual squared inverse current-line scale when transferring
the genuine observed diagonal jet to the original raw model basis.
Source: the true spectral norm of a diagonal matrix and scalar product
splitting; all scalar bounds will be supplied by the actual native theorems.
-/
namespace krylov.Functions
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Genuine diagonal spectral coordinates have the exact finite scalar source bound.
Article: main_krylov, prop:Fcycle, observed model-size control. -/
theorem diagonal_scalar_product_norm (x a : Fin n → ℝ) (R M : ℝ)
    (hR : 0≤R) (hM : 0≤M) (hx : ∀ i,|x i|≤R) (ha : ∀ i,|a i|≤M) :
    ‖Matrix.diagonal (fun i=>x i*a i)‖≤M*R := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hR)).mpr
  intro i
  simpa only [Real.norm_eq_abs,abs_mul,mul_comm] using mul_le_mul (hx i) (ha i) (abs_nonneg _) hR

/-- A true observed diagonal jet and the actual inverse-square coordinate jet
retain their full error after the original raw-model change of basis.
Article: main_krylov, prop:Fcycle, normalized last-column substitution. -/
theorem diagonal_scalar_product_jet (x y a b : Fin n → ℝ) (ε J M B V : ℝ)
    (hε : 0≤ε) (hJ : 0≤J) (hM : 0≤M) (hB : 0≤B) (hV : 0≤V)
    (hx : ∀ i,|x i-ε*y i|≤J) (ha : ∀ i,|a i|≤M)
    (hy : ∀ i,|y i|≤B) (hab : ∀ i,|a i-b i|≤V) :
    ‖Matrix.diagonal (fun i=>x i*a i)-ε • Matrix.diagonal (fun i=>y i*b i)‖≤M*J+ε*B*V := by
  have he : Matrix.diagonal (fun i=>x i*a i)-ε • Matrix.diagonal (fun i=>y i*b i)=
      Matrix.diagonal (fun i=>(x i-ε*y i)*a i+ε*y i*(a i-b i)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,diagonal_apply_eq]
      ring
    · simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,diagonal_apply_ne _ hij,mul_zero,sub_self]
  rw [he,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤M*J+ε*B*V)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |(x i-ε*y i)*a i| + |ε*y i*(a i-b i)| := abs_add_le _ _
    _ = |x i-ε*y i| * |a i| + ε*|y i| * |a i-b i| := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hε]
    _ ≤ J*M+ε*B*V := add_le_add (mul_le_mul (hx i) (ha i) (abs_nonneg _) hJ)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hy i) hε) (hab i) (abs_nonneg _) (mul_nonneg hε hB))
    _ = _ := by ring

/-- The actual normalized raw value-model change has its genuine observed diagonal norm bound.
Article: main_krylov, prop:Fcycle, source bound before the new query is enclosed. -/
theorem rfcFNormalizedRawValueChange_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (k : ℕ)
    (ε : ℝ) (c : Fin (k+1) → ℝ) (R M : ℝ) (hR : 0≤R) (hM : 0≤M)
    (hd : ∀ i,|rfcFNormalizedValueDiagonal T f G r x₀ k ε i|≤R)
    (hc : ∀ i,|(c i)⁻¹^2|≤M) :
    ‖rfcFNormalizedRawValueChange T f G r x₀ k ε c‖≤M*R := by
  have he : rfcFNormalizedRawValueChange T f G r x₀ k ε c=
      Matrix.diagonal (fun i=>rfcFNormalizedValueDiagonal T f G r x₀ k ε i.rev*(c i)⁻¹^2) := by
    simp only [rfcFNormalizedRawValueChange,div_eq_mul_inv,inv_pow]
  rw [he]
  exact diagonal_scalar_product_norm _ _ R M hR hM (fun i=>hd i.rev) hc

end
end krylov.Functions
