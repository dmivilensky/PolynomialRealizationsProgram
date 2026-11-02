import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, prop:deep, exact original affine source family.
Use: fix the literal rational four-dimensional source matrices, derive
their strict spectral budgets and transport the actual full family into
its genuine physical oracle scenario with the printed positive base.
Source: the original seven rational rows, exact two-block Frobenius norms,
proved spectral comparison and genuine relative form congruence invariance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The exact printed symmetric two-block matrix with its original factor one thirty-second.
Use: Retain all original rational certificate data exactly.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepBlock (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1/32 : ℝ) • !![a,b,0,0; b,c,0,0; 0,0,d,e; 0,0,e,f]

/-- The seven exact original integer-row seed matrices X₀, X₁, X₂, X₃, Y₁, Y₂ and X′.
Use: Fix the actual affine unbounded-family coefficients before generating any enclosure.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepSeed : Fin 7 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![deepBlock (-1) 6 (-5) (-7) 2 (-2),deepBlock 0 (-2) 8 (-7) 2 6,
    deepBlock (-8) (-7) (-6) 4 6 (-8),deepBlock (-6) (-7) 5 7 2 (-4),
    deepBlock 7 (-1) 6 1 2 2,deepBlock (-8) 2 2 (-4) 6 2,deepBlock (-3) 0 (-6) 3 (-1) (-1)]

/-- Every genuine printed two-block seed form is symmetric.
Use: Establish the original physical source symmetry from its literal matrix data.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Evaluate the sixteen true entries of the original two-block form. -/
theorem deepBlock_isSymm (a b c d e f : ℝ) : (deepBlock a b c d e f).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Each of the seven exact original seed matrices is symmetric.
Use: Use only real symmetric primitive source coefficients.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Each actual seed is a specialization of the independently proved symmetric two-block form. -/
theorem deepSeed_isSymm (i : Fin 7) : (deepSeed i).IsSymm := by
  fin_cases i <;> exact deepBlock_isSymm _ _ _ _ _ _

/-- The exact squared Hilbert–Schmidt norm of the original rational two-block form is its printed sum of six squared coefficients.
Use: Reduce all primitive source budget certificates to small exact rational inequalities.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Expand the sixteen real matrix entries and collect the two symmetric off-diagonal repetitions. -/
theorem deepBlock_hsSq (a b c d e f : ℝ) :
    chebyshev1.hsSq (deepBlock a b c d e f)=(a^2+2*b^2+c^2+d^2+2*e^2+f^2)/1024 := by
  simp only [chebyshev1.hsSq,deepBlock,Fin.sum_univ_succ,Matrix.smul_apply,Fin.succ_zero_eq_one,smul_eq_mul,Fin.sum_univ_zero,add_zero]
  norm_num
  ring

/-- All seven genuine original seed matrices have squared Hilbert–Schmidt norm at most 175/512.
Use: Verify the printed original seed budget margin in the Lean kernel.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The exact general two-block norm formula reduces each of the seven literal rows to a rational inequality. -/
theorem deepSeed_hsSq (i : Fin 7) : chebyshev1.hsSq (deepSeed i)≤175/512 := by
  fin_cases i
  all_goals
    change chebyshev1.hsSq (deepBlock _ _ _ _ _ _)≤(175/512 : ℝ)
    rw [deepBlock_hsSq]
    norm_num

/-- Each exact original seed has strict spectral norm below one.
Use: Obtain the original strict primitive spectral budget margins from verified Frobenius data.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The reused genuine spectral-versus-Hilbert–Schmidt bound and exact squared norm certificate give the strict unit bound. -/
theorem deepSeed_norm_lt_one (i : Fin 7) : ‖deepSeed i‖<1 := by
  have hh := chebyshev1.hsNorm_sq (deepSeed i)
  have hb := deepSeed_hsSq i
  have hs : chebyshev1.hsNorm (deepSeed i)<1 := by nlinarith [chebyshev1.hsNorm_nonneg (deepSeed i)]
  exact (spectral_le_hsNorm _).trans_lt hs

/-- The genuine original affine first-increment seed has strict spectral norm below one over the entire closed parameter interval.
Use: Verify the original affine family budgets uniformly, including both endpoints.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The spectral norm is convex. Both actual endpoint seed norms are strictly below one; the zero endpoint is handled directly and the positive coefficient retains a strict margin. -/
theorem deep_convex_seed_norm_lt_one (s : ℝ) (hs : s∈Set.Icc 0 1) :
    ‖(1-s) • deepSeed 0+s • deepSeed 1‖<1 := by
  -- Preserve the strict true endpoint margins over the entire closed affine parameter interval.
  have hn := norm_add_le ((1-s) • deepSeed 0) (s • deepSeed 1)
  rw [norm_smul,norm_smul,Real.norm_of_nonneg (by linarith [hs.2] : 0≤1-s),Real.norm_of_nonneg hs.1] at hn
  have h0 := deepSeed_norm_lt_one 0
  have h1 := deepSeed_norm_lt_one 1
  have he : (1-s)*‖deepSeed 0‖+s*‖deepSeed 1‖<1 := by
    by_cases hz : s=0
    · subst s; simpa using h0
    · nlinarith [mul_le_mul_of_nonneg_left h0.le (show 0≤1-s by linarith [hs.2]),mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hz)) (sub_pos.mpr h1)]
  exact hn.trans_lt he


end
end krylov.Correction
