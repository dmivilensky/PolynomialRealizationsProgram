import krylov.Correction.ReferenceOperator
import krylov.Variation.FCResponse

/-!
Article: main_krylov, thm:C, true CG coordinates of the two leading factors.
Use: identify the native chronological pairing coefficients with the genuine
fresh defect and staircase, reusing the existing actual finite CG flag calculus.
Source: true old-flag projection selection, actual zero-safe step normalization
and finite summation of the original canonical increments.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- An actual canonical CG step is retained or annihilated by its true chronological old flag.
Use: simplify both sides of the staircase compression using genuine computed reference steps.
Article: main_krylov, thm:C, P_l s_i=1_(i≤l)s_i.
Proof: use actual normalized-step membership when the flag contains its index;
otherwise true finite-prefix CG orthogonality makes its projection vanish. -/
theorem canonicalStep_oldFlag_projection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    {i : ℕ} (hi : i<N) (l : ℕ) :
    (oldFlag base g l).starProjection (canonicalCGStep base g i)=
      if i≤l then canonicalCGStep base g i else 0 := by
  -- Retain the actual step norm outside the zero-safe normalized reference projection.
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i :=
    (NormedSpace.norm_smul_normalize _).symm
  by_cases hil : i≤l
  · rw [ite_eq_left hil]
    exact Submodule.starProjection_eq_self_iff.mpr
      (hs ▸ (oldFlag base g l).smul_mem _ (unitStep_mem_oldFlag base g hil))
  · rw [ite_eq_right hil,hs,map_smul]
    have hp : (oldFlag base g l).starProjection (canonicalCGUnitStep base g i)=0 := by
      change ((oldFlag base g l).orthogonalProjectionOnto (canonicalCGUnitStep base g i) :
        EuclideanSpace ℝ (Fin n))=0
      rw [(oldFlag base g l).orthogonalProjectionOnto_eq_zero_iff.mpr
        (unitStep_prefix_oldFlag_orthogonal base hb g hN hi (by omega))]
      rfl
    rw [hp,smul_zero]

/-- The actual CG-step matrix entry of the staircase selects exactly the common chronological increment tail.
Use: identify the leading latest-model error without introducing a second flag basis.
Article: main_krylov, thm:C, U₀ᵀ𝓛U₀ and its later-observation convention.
Proof: each true orthogonal compression keeps an entry precisely when both
step indices belong to its flag. The surviving finite range is their common
half-open suffix; linearity combines its actual increment matrices. -/
theorem staircase_step_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    {i j : ℕ} (hi : i<N) (hj : j<N) :
    inner ℝ (canonicalCGStep base g i) (staircaseOperator base g E F N (canonicalCGStep base g j))=
      inner ℝ (canonicalCGStep base g i)
        (cgOperator (F+∑ l∈Ico (max i j) (N-1), E l) (canonicalCGStep base g j)) := by
  -- An entry survives exactly the intersection of its two chronological old flags.
  have ht (l : ℕ) : inner ℝ (canonicalCGStep base g i)
      ((oldFlag base g l).starProjection (cgOperator (E l)
        ((oldFlag base g l).starProjection (canonicalCGStep base g j))))=
      if max i j≤l then inner ℝ (canonicalCGStep base g i)
        (cgOperator (E l) (canonicalCGStep base g j)) else 0 := by
    rw [step_inner_oldFlag_prefix base hb g hN hi,
      canonicalStep_oldFlag_projection base hb g hN hj]
    by_cases hil : i≤l <;> by_cases hjl : j≤l <;>
      simp only [hil,hjl,max_le_iff,ite_true,ite_false,map_zero,inner_zero_right,and_self,
        false_and,and_false]
  rw [staircaseOperator_apply,inner_add_right,inner_sum]
  simp_rw [ht]
  rw [← sum_filter]
  have hset : (range (N-1)).filter (fun l => max i j≤l)=Ico (max i j) (N-1) := by
    ext l
    simp only [mem_filter,mem_range,mem_Ico,and_comm]
  rw [hset]
  simp only [cgOperator,map_add,_root_.add_apply,map_sum,_root_.sum_apply,inner_add_right,inner_sum]
  exact add_comm _ _

/-- The scaled actual fresh defect has precisely the true cumulative-drift step coordinates.
Use: identify the native incoming right-hand side with the source's true last-step energy scale.
Article: main_krylov, thm:C, √c_last Qᵀf̂.
Proof: reuse the previously proved actual fresh-defect coordinate suffix;
move the actual last-step norm into its zero-safe normalized step and sum the true increment actions. -/
theorem freshDefect_scaled_step_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : i<N) :
    inner ℝ (canonicalCGStep base g i)
      (‖canonicalCGStep base g (N-1)‖ • freshDefect base g E N)=
      inner ℝ (canonicalCGStep base g i)
        (cgOperator (∑ l∈Ico i (N-1), E l) (canonicalCGStep base g (N-1))) := by
  -- Move the true terminal step energy into each actual normalized last-step action.
  rw [real_inner_smul_right,freshDefect_step_coordinate base hb g hN E i hi,Finset.mul_sum]
  simp only [cgOperator,map_sum,_root_.sum_apply,inner_sum]
  apply sum_congr rfl
  intro l _
  rw [← real_inner_smul_right,← map_smul]
  congr 2
  exact NormedSpace.norm_smul_normalize _

end
end krylov.Correction
