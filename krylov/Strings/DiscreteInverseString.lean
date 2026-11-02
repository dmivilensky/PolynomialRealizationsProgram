import krylov.Strings.DiscreteInverseRow
import chebyshev2.Finite.MatrixExt

/-!
Article: `main_krylov`, `apC:lem:stieltjes(b)`.
Construct actual positive masses and gaps and the nonnegative Robin
boundary from arbitrary nonnegative finite spectral probability data.
The resulting genuine physical path operator is proved equal, after its
actual alternating conjugacy, to the independently reconstructed Jacobi
operator of those prescribed data.
-/

namespace krylov.Strings.DiscreteInverse
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- Genuine finite string reconstructed from the prescribed positive
probability measure, with every physical positivity obligation proved. -/
def string (hnode : ∀ i,0≤M.node i) : DiscreteString N where
  mass k := zeroValue M k^2
  gap k := (coupling M k*zeroValue M k*zeroValue M (k+1))⁻¹
  mass_zero := by rw [zeroValue_zero]; norm_num
  mass_pos k _ := sq_pos_of_pos (zeroValue_pos M hnode k)
  gap_pos k hk := inv_pos.mpr
    (mul_pos (mul_pos (coupling_pos M k hk) (zeroValue_pos M hnode k))
      (zeroValue_pos M hnode (k+1)))
  robin := robin M
  robin_nonneg := robin_nonneg M hnode

@[simp] theorem string_mass (hnode : ∀ i,0≤M.node i) (k : ℕ) :
    (string M hnode).mass k=zeroValue M k^2 := rfl
@[simp] theorem string_gap (hnode : ∀ i,0≤M.node i) (k : ℕ) :
    (string M hnode).gap k=(coupling M k*zeroValue M k*zeroValue M (k+1))⁻¹ := rfl
@[simp] theorem string_robin (hnode : ∀ i,0≤M.node i) :
    (string M hnode).robin=robin M := rfl

/-- The square-root mass normalization is exactly the constructed positive
zero-energy value, including all physical sites. -/
theorem sqrt_string_mass (hnode : ∀ i,0≤M.node i) (k : ℕ) :
    Real.sqrt ((string M hnode).mass k)=zeroValue M k := by
  rw [string_mass, Real.sqrt_sq (zeroValue_pos M hnode k).le]

/-- Exact adjacent coupling of the actual reconstructed physical string. -/
theorem string_positiveOperator_adjacent (hnode : ∀ i,0≤M.node i)
    (i j : Fin (N+1)) (hij : i.val+1=j.val) :
    (string M hnode).positiveOperator i j=coupling M i.val := by
  rw [(string M hnode).positiveOperator_adjacent i j hij,
    (string M hnode).operator_adjacent i j hij, sqrt_string_mass, sqrt_string_mass,
    string_gap, inv_inv, ← hij]
  field_simp [(zeroValue_pos M hnode i.val).ne', (zeroValue_pos M hnode (i.val+1)).ne']

/-- The actual mass-gap diagonal agrees with the same independently
constructed canonical Jacobi diagonal at every physical site. -/
theorem string_operator_diagonal (hnode : ∀ i,0≤M.node i) (i : Fin (N+1)) :
    (string M hnode).operator i i=M.reconstructed.data.b i.val := by
  rw [(string M hnode).operator_diagonal]
  simp only [string_gap, string_mass, string_robin, inv_inv]
  have hq := (zeroValue_pos M hnode i.val).ne'
  by_cases hi : i.val<N
  · rw [ite_eq_left hi, ite_eq_right (by omega : i.val≠N)]
    have hb := zeroValue_balance M i.val hi
    by_cases hi0 : 0 < i.val
    · rw [ite_eq_left hi0, show i.val-1+1=i.val by omega]
      have hk0 : i.val≠0 := by omega
      rw [ite_eq_right hk0] at hb
      field_simp
      nlinarith [hb]
    · rw [ite_eq_right hi0]
      have hk0 : i.val=0 := by omega
      rw [ite_eq_left hk0] at hb
      field_simp
      nlinarith [hb]
  · have hil : i.val=N := by omega
    rw [ite_eq_right hi, ite_eq_left hil, hil, robin]
    by_cases hN : 0<N
    · rw [ite_eq_left hN, ite_eq_left hN, show N-1+1=N by omega]
      field_simp [(zeroValue_pos M hnode N).ne']
      ring
    · rw [ite_eq_right hN, ite_eq_right hN]
      field_simp [(zeroValue_pos M hnode N).ne']
      ring

/-- Actual inverse Stieltjes realization: the physical path form, after
its genuine alternating sign conjugacy, is exactly the canonical Jacobi
matrix reconstructed from the prescribed measure. -/
theorem string_positiveOperator (hnode : ∀ i,0≤M.node i) :
    (string M hnode).positiveOperator=M.reconstructed.matrix := by
  ext i j
  by_cases hij : i=j
  · subst j
    rw [(string M hnode).positiveOperator_apply, string_operator_diagonal]
    have hs := alternating_sq i.val
    simp only [Jacobi.matrix, JacobiData.matrix_apply, ite_true, Nat.zero_add]
    linear_combination M.reconstructed.data.b i.val*hs
  · by_cases hu : i.val+1=j.val
    · rw [string_positiveOperator_adjacent M hnode i j hu]
      simp only [Jacobi.matrix, JacobiData.matrix_apply, ite_eq_right hij,
        Nat.zero_add, coupling, hu, ite_true]
    · by_cases hl : j.val+1=i.val
      · rw [← ((string M hnode).positiveOperator_isHermitian.isSymm.apply i j),
          string_positiveOperator_adjacent M hnode j i hl]
        simp only [Jacobi.matrix, JacobiData.matrix_apply, ite_eq_right hij,
          ite_eq_right hu, Nat.zero_add, coupling, hl, ite_true]
      · have hfar : i.val+1<j.val ∨ j.val+1< i.val := by
          have hne : i.val≠j.val := by intro he; exact hij (Fin.ext he)
          omega
        rw [(string M hnode).positiveOperator_tridiagonal i j hfar]
        rw [M.reconstructed_matrix, M.multiplication_tridiagonal i j hfar]

/-- Encoding the actual inverse physical string recovers exactly the
independently constructed canonical Jacobi object. -/
theorem string_jacobi (hnode : ∀ i,0≤M.node i) :
    (string M hnode).jacobi=M.reconstructed := by
  apply Jacobi.matrix_injective
  rw [(string M hnode).jacobi_matrix, string_positiveOperator]

end
end krylov.Strings.DiscreteInverse
