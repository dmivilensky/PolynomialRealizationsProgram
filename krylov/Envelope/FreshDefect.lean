import krylov.Envelope.PrefixResponseCoordinates
import krylov.Envelope.FlagOrthogonality

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, genuine finite-horizon fresh defect.
Use: construct the actual source fresh old-flag response and identify
its true canonical step coordinates and final-direction orthogonality.
Source: actual finite CG old flags and genuine nonstagnating orthogonal
projection coordinate identities, including real empty sums.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine finite-horizon fresh defect sums actual old-flag projections of the real source increments acting on the true last CG unit step.
Use: The genuine finite-horizon fresh defect sums actual old-flag projections of the real source increments acting on the true last CG unit step.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, genuine finite-horizon fresh defect.
Proof: Use exactly the true meaningful chronological source increment range. -/
def freshDefect (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈range (N-1), (oldFlag base g l).starProjection (cgOperator (E l) (canonicalCGUnitStep base g (N-1)))

/-- The actual fresh defect belongs to the genuine strictly earlier explored CG flag.
Use: The actual fresh defect belongs to the genuine strictly earlier explored CG flag.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, genuine finite-horizon fresh defect.
Proof: Every real old projection lies in its true earlier flag, contained in the actual horizon predecessor flag. -/
theorem freshDefect_mem (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    freshDefect base g E N∈exploredFlag base g (N-1) := by
  -- Each actual old projection lies in a genuine earlier CG flag, which embeds in the true predecessor explored flag.
  apply Submodule.sum_mem
  intro l hl
  have hle : oldFlag base g l≤exploredFlag base g (N-1) := by
    apply Submodule.span_le.mpr
    rintro v ⟨j,hj,rfl⟩
    change j≤l at hj
    have hjN : j<N-1 := by have := mem_range.mp hl;omega
    exact Submodule.subset_span ⟨(⟨j,hjN⟩ : Fin (N-1)),rfl⟩
  exact hle ((oldFlag base g l).starProjection_apply_mem _)

/-- Each genuine canonical CG step pairs with the actual fresh defect through exactly the true chronological increment suffix.
Use: Each genuine canonical CG step pairs with the actual fresh defect through exactly the true chronological increment suffix.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, genuine finite-horizon fresh defect.
Proof: Use the real old-projection coordinate identity and identify the genuine retained finite suffix indices. -/
theorem freshDefect_step_coordinate (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (hi : i<N) :
    inner ℝ (canonicalCGStep base g i) (freshDefect base g E N)=
      ∑ l∈Ico i (N-1), inner ℝ (canonicalCGStep base g i)
        (cgOperator (E l) (canonicalCGUnitStep base g (N-1))) := by
  unfold freshDefect
  rw [inner_sum]
  simp_rw [step_inner_oldFlag_prefix base hb g hN hi]
  rw [← sum_filter]
  congr 1
  ext l
  simp only [mem_filter,mem_range,mem_Ico,and_comm]

/-- The actual final canonical CG step is orthogonal to the genuine fresh defect on every true active horizon.
Use: The actual final canonical CG step is orthogonal to the genuine fresh defect on every true active horizon.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, genuine finite-horizon fresh defect.
Proof: Its genuine chronological fresh coordinate suffix is empty. -/
theorem freshDefect_last_coordinate_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hpos : 0<N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (canonicalCGStep base g (N-1)) (freshDefect base g E N)=0 := by
  rw [freshDefect_step_coordinate base hb g hN E (N-1) (by omega),Ico_self,sum_empty]
end
end krylov.Envelope
