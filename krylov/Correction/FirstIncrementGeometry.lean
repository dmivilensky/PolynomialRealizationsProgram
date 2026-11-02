import krylov.Correction.ModifiedScenarioTube

/-!
Article: main_krylov, thm:C2(c), exact genuine one-increment leading geometry.
Use: identify the actual informed modified-solve coefficient with the true
hidden original first CG diagonal and the true observed terminal cross entry.
Source: genuine first CG flag, unit singleton orthogonal projection and
the exact original finite fresh-defect and staircase definitions.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Methods krylov.Stability krylov.LinearAlgebra krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual source increment sequence with exactly one possibly nonzero first increment.
Use: the known-base theorem's primitive perturbation model is kept separate from independent intermediate correction defects.
Article: main_krylov, thm:C2(c), E_l=1_{l=0}E₀. -/
def firstIncrement (M : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if i=0 then M else 0

/-- The genuine first CG old flag is the actual span of its computed first unit step.
Use: one-increment leading terms use the exact source flag rather than an assumed rank-one projector.
Article: main_krylov, thm:C2(c), P₀ projects onto span{ŝ₀}.
Proof: the actual natural-number prefix through zero contains exactly zero. -/
theorem oldFlag_zero (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    oldFlag base g 0=ℝ ∙ canonicalCGUnitStep base g 0 := by
  have hz : Set.Iic (0 : ℕ)={0} := by ext i; simp
  simp only [oldFlag,hz,Set.image_singleton]

/-- The actual first CG flag has its exact true unit rank-one projection action.
Use: derive the source's hidden diagonal and terminal cross scalar directly from the original matrix.
Article: main_krylov, thm:C2(c), P₀v=⟨ŝ₀,v⟩ŝ₀.
Proof: the genuine old flag is the true unit singleton span; reuse mathlib's exact orthogonal projection formula. -/
theorem oldFlag_zero_apply (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (he : ‖canonicalCGUnitStep base g 0‖=1) (v : EuclideanSpace ℝ (Fin n)) :
    (oldFlag base g 0).starProjection v=(inner ℝ (canonicalCGUnitStep base g 0) v) • canonicalCGUnitStep base g 0 := by
  rw [oldFlag_zero]
  exact Submodule.starProjection_unit_singleton ℝ he v

/-- With only the original first increment present, the genuine fresh vector is exactly the original terminal cross scalar times the true first CG unit step.
Use: expose the one-increment actual leading coefficient without an abstract supplied fresh vector.
Article: main_krylov, thm:C2(c), f̂=(ŝ₀ᵀE₀ŝ_last)ŝ₀.
Proof: every genuine source increment except zero vanishes. The actual
finite fresh sum therefore contains one true first-flag action, whose exact
unit projection formula gives the original terminal cross entry.
-/
theorem firstIncrement_fresh {N : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hN : 0<N) (he : ‖canonicalCGUnitStep base g 0‖=1) (M : Matrix (Fin n) (Fin n) ℝ) :
    freshDefect base g (firstIncrement M) (N+1)=
      (inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g N))) • canonicalCGUnitStep base g 0 := by
  -- Retain the source's actual N increment slots and its genuine terminal direction N.
  simp only [freshDefect,Nat.add_sub_cancel]
  rw [sum_eq_single 0]
  · simp only [firstIncrement,ite_true]
    exact oldFlag_zero_apply base g he _
  · intro i _ hi
    simp only [firstIncrement,ite_eq_right hi,cgOperator,map_zero,_root_.zero_apply,map_zero]
  · intro hz
    exact (hz (mem_range.mpr hN)).elim

/-- The actual single-first-increment staircase acts on its genuine fresh vector through exactly the original hidden first diagonal and terminal cross scalar.
Use: the actual ordinary RFC quadratic leading coefficient has its concrete original matrix-entry form.
Article: main_krylov, thm:C2(c), 𝓛f̂=(ŝ₀ᵀE₀ŝ₀)(ŝ₀ᵀE₀ŝ_last)ŝ₀.
Proof: the genuine staircase sum has only its original first compression.
The true fresh vector lies in that exact unit flag; two actual rank-one
projection actions leave precisely the two printed original scalar entries.
-/
theorem firstIncrement_staircase_fresh {N : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hN : 0<N) (he : ‖canonicalCGUnitStep base g 0‖=1) (M : Matrix (Fin n) (Fin n) ℝ) :
    staircaseOperator base g (firstIncrement M) 0 (N+1) (freshDefect base g (firstIncrement M) (N+1))=
      ((inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g 0)))*
        inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g N))) • canonicalCGUnitStep base g 0 := by
  -- Evaluate the same genuine single source compression on its actual fresh vector.
  rw [staircaseOperator_apply]
  simp only [Nat.add_sub_cancel,cgOperator,map_zero,_root_.zero_apply,add_zero]
  rw [sum_eq_single 0]
  · simp only [firstIncrement,ite_true]
    rw [firstIncrement_fresh base g hN he M]
    have hee : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g 0)=1 := by
      rw [real_inner_self_eq_norm_sq,he,one_pow]
    simp only [oldFlag_zero_apply base g he,map_smul,real_inner_smul_right,hee,mul_one]
    congr 1
    dsimp only [cgOperator]
    ring
  · intro i _ hi
    simp only [firstIncrement,ite_eq_right hi,map_zero,_root_.zero_apply]
  · intro hz
    exact (hz (mem_range.mpr hN)).elim

end
end krylov.Correction
