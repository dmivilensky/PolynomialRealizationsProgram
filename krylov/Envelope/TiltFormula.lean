import krylov.Envelope.CanonicalInjectionPairing
import krylov.Envelope.DirectionTiltGeometry

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), genuine printed double-sum common tilt.
Use: identify the actual frozen common tilt with the explicit source
measured direction-polynomial double sum, including its true early
increment bounds, genuine step energies and empty-horizon conventions.
Source: real measured frozen direction impulses, actual canonical
injection pairings and true finite triangular sum interchange.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine printed common-tilt double sum over actual earlier cumulative increments and true later measured CG steps.
Use: The genuine printed common-tilt double sum over actual earlier cumulative increments and true later measured CG steps.
Article: main_krylov, apB:lem:mu(b), genuine printed double-sum common tilt.
Proof: Use actual continuation-direction vectors, real CG line lengths and genuine square-root energy normalizations on the true finite chronological triangle. -/
def canonicalTiltSum (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ p∈Ico 1 (N-1), ∑ i∈Ico (p+1) N,
    (CG.length (cgOperator base) g i*Real.sqrt (cgEnergy base g p)/Real.sqrt (cgEnergy base g i)*
      inner ℝ (directionTiltVector base g N i p)
        (cgOperator (∑ l∈range p,E l) (canonicalCGUnitStep base g p))) • canonicalCGUnitStep base g i

/-- The genuine actual common frozen tilt equals exactly the printed true direction-polynomial increment double sum.
Use: The genuine actual common frozen tilt equals exactly the printed true direction-polynomial increment double sum.
Article: main_krylov, apB:lem:mu(b), genuine printed double-sum common tilt.
Proof: Unroll real frozen direction impulses and identify their actual canonical pairings. Genuine step-energy normalization gives every true source coefficient; interchange the actual finite triangle and remove only the genuine zero first increment and empty final tail. -/
theorem commonTilt_canonical_formula (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    commonTilt base g (canonicalFCPath base E) N=canonicalTiltSum base g E N := by
  -- First identify each genuine measured frozen coordinate before exchanging the actual finite chronological sums.
  let f := fun p i : ℕ => (CG.length (cgOperator base) g i*Real.sqrt (cgEnergy base g p)/Real.sqrt (cgEnergy base g i)*
      inner ℝ (directionTiltVector base g N i p)
        (cgOperator (∑ l∈range p,E l) (canonicalCGUnitStep base g p))) • canonicalCGUnitStep base g i
  have hs (p : ℕ) : canonicalCGStep base g p=Real.sqrt (cgEnergy base g p) • canonicalCGUnitStep base g p := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  have hfirst : commonTilt base g (canonicalFCPath base E) N=∑ i∈range N, ∑ p∈range i,f p i := by
    unfold commonTilt
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [frozen_displacement_step,real_inner_smul_right,frozen_direction_formula]
    simp only [inner_sum,Finset.mul_sum,Finset.sum_div,Finset.sum_smul]
    apply sum_congr rfl
    intro p _
    rw [canonical_injection_pairing base hb g E N p,hs p,map_smul,real_inner_smul_right,← cgEnergy_sqrt base hb g i.val]
    change (_ : ℝ) • canonicalCGUnitStep base g i.val=f p i.val
    dsimp only [f,directionTiltVector]
    congr 1
    ring
  -- Interchange the true finite earlier-increment/later-step triangle, keeping the actual empty boundary contributions explicit.
  have hswap : (∑ i∈range N, ∑ p∈range i,f p i)=∑ p∈range N, ∑ i∈Ico (p+1) N,f p i := by
    simpa only [Nat.Ico_zero_eq_range] using (sum_Ico_Ico_comm' 0 N f).symm
  have htrim : (∑ p∈range N, ∑ i∈Ico (p+1) N,f p i)=∑ p∈Ico 1 (N-1), ∑ i∈Ico (p+1) N,f p i := by
    symm
    apply sum_subset (by intro p hp;have := mem_Ico.mp hp;exact mem_range.mpr (by omega))
    intro p hp hnot
    by_cases hz : p=0
    · subst p
      simp only [f,range_zero,sum_empty,cgOperator,map_zero,_root_.zero_apply,inner_zero_right,mul_zero,zero_smul,sum_const_zero]
    · have he : p+1=N := by have := mem_range.mp hp;simp only [mem_Ico,not_and_or,not_le] at hnot;omega
      simp only [he,Ico_self,sum_empty]
  rw [hfirst,hswap,htrim]
  rfl
end
end krylov.Envelope
