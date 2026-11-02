import krylov.Stability.CanonicalFCOperators
import krylov.Stability.ObliqueResponse
import krylov.Methods.DirectionStaircase
import krylov.Variation.ResponseCoordinates

/-!
Article: main_krylov, thm:A and apB:lem:UArem, exact genuine FC oblique reconstruction.
Use: reconstruct the actual full-cycle residual from the true executed
normalized direction basis and identify its reference value with the actual first response.
Source: the genuine direction staircase, canonical metric drift pairing,
actual CG orthogonality and the proved exact oblique coordinate summation.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual defined FC residual is exactly its genuine direction-basis oblique response.
Use: The actual defined FC residual is exactly its genuine direction-basis oblique response.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Transfer the real staircase to canonical coordinates; normalize actual nonzero direction rows and use the proved true basis domain and coordinate uniqueness. -/
theorem fullFC_exact_oblique_response (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) (g : EuclideanSpace ℝ (Fin n))
    (hsolve : ∀ i<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))).det)
    (hcurv : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath base E 1) g i)
      (canonicalFCPath base E 1 i (fcDirection fullMemory (canonicalFCPath base E 1) g i))≠0)
    (hsmall : (n : ℝ)*(∑ l∈range n, ‖E l‖)≤1/2) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory (canonicalFCPath base E 1) g n)=
      obliqueResponse (canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g) E
        (fun j => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory (canonicalFCPath base E 1) g j)) := by
  -- Reconstruct from real normalized directions; the final actual line displacement may vanish.
  let A := canonicalFCPath base E 1
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let T := canonicalFCDirectionMatrix base A g
  apply obliqueResponse_unique T (canonicalFCPath_directionMatrix_unit base hb E g hsolve hcurv hsmall)
  intro i
  have hrow := fullFC_direction_staircase A g n
    (fun j _ => canonicalFCPath_symmetric base hb E hE 1 j) hsolve hcurv i.isLt
  change inner ℝ (NormedSpace.normalize (R (fcDirection fullMemory A g i.val)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g n))=
    ∑ j∈Ico (i.val+1) n, inner ℝ (NormedSpace.normalize (R (fcDirection fullMemory A g i.val)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Ico i.val j, E l) (R (fcStep fullMemory A g j)))
  rw [NormedSpace.normalize,real_inner_smul_left,← canonical_search_pairing base hb,hrow,Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  have hij : i.val≤j := by have := (mem_Ico.mp hj).1; omega
  have hdiff : A j-A i.val=Matrix.toEuclideanCLM (𝕜 := ℝ)
      (metricRoot base*(∑ l∈Ico i.val j, E l)*metricRoot base) := by
    dsimp only [A,canonicalFCPath]
    simp only [one_smul,add_sub_add_left_eq_sub]
    exact cumulativeDrift_sub base E hij
  rw [hdiff,metric_drift_pairing,real_inner_smul_left]

/-- The square matrix of genuine normalized canonical CG steps.
Use: The square matrix of genuine normalized canonical CG steps.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Its columns use the already defined actual reference steps. -/
def canonicalCGUnitMatrix (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => canonicalCGUnitStep base g j.val i

/-- The full-active genuine CG unit-step matrix is orthogonal.
Use: The full-active genuine CG unit-step matrix is orthogonal.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Use the actual CG old-step Gram identity through the full active count. -/
theorem canonicalCGUnitMatrix_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n) :
    (canonicalCGUnitMatrix base g)ᵀ*canonicalCGUnitMatrix base g=1 := by
  rw [transpose_mul_columnGram]
  exact canonicalCG_old_gram base hb g n hcount.symm.le

/-- The full-active actual reference unit-step matrix is nonsingular.
Use: The full-active actual reference unit-step matrix is nonsingular.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Its genuine Gram error is zero. -/
theorem canonicalCGUnitMatrix_unit (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n) :
    IsUnit (canonicalCGUnitMatrix base g).det := by
  apply column_unit_of_near_gram
  rw [canonicalCGUnitMatrix_gram base hb g hcount,sub_self,norm_zero]
  norm_num

/-- The full-active actual reference unit-step inverse is its transpose.
Use: The full-active actual reference unit-step inverse is its transpose.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: The proved actual left inverse is the genuine matrix inverse. -/
theorem canonicalCGUnitMatrix_inverse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n) :
    (canonicalCGUnitMatrix base g)⁻¹=(canonicalCGUnitMatrix base g)ᵀ :=
  Matrix.inv_eq_left_inv (canonicalCGUnitMatrix_gram base hb g hcount)

/-- The true reference oblique response equals the already proved actual FC first response.
Use: The true reference oblique response equals the already proved actual FC first response.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Compare true step pairings, multiply normalized reference coordinates by their own actual step lengths and use the exact genuine response coordinates. -/
theorem canonicalCG_obliqueResponse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    obliqueResponse (canonicalCGUnitMatrix base g) E (canonicalCGStep base g)=
      fullCycleResponse base g (range n) E := by
  -- Each actual reference length cancels inside its own pairing, without a uniform lower bound.
  let Q := canonicalCGUnitMatrix base g
  have hu := canonicalCGUnitMatrix_unit base hb g hcount
  apply canonical_step_inner_ext base hb g hcount
  intro i hi
  let j : Fin n := ⟨i,hi⟩
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • WithLp.toLp 2 (fun a => Q a j) :=
    (NormedSpace.norm_smul_normalize _).symm
  calc
    _ = ‖canonicalCGStep base g i‖*inner ℝ (WithLp.toLp 2 (fun a => Q a j))
        (obliqueResponse Q E (canonicalCGStep base g)) := by conv_lhs => rw [hs,real_inner_smul_left]
    _ = ‖canonicalCGStep base g i‖*(∑ k∈Ico (i+1) n, inner ℝ (WithLp.toLp 2 (fun a => Q a j))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Ico i k, E l) (canonicalCGStep base g k))) :=
      congrArg (fun r => ‖canonicalCGStep base g i‖*r) (obliqueResponse_coordinates Q hu E _ j)
    _ = ∑ k∈Ico (i+1) n, inner ℝ (canonicalCGStep base g i)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈Ico i k, E l) (canonicalCGStep base g k)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro k _
      conv_rhs => rw [hs,real_inner_smul_left]
    _ = _ := (fullCycleResponse_coordinates base hb g hcount E hi).symm
end
end krylov.Stability
