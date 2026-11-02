import krylov.Envelope.FinalErrorImage
import krylov.Reference.EnergyPositive
import krylov.Stability.CanonicalContinuity

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:Ahe and thm:select, actual final-error image norm.
Use: compute the true two-neighbor energy formula for the genuine
base-image norm and its actual nonzero before-exhaustion domain.
Source: proved genuine neighboring CG step representation, actual CG
orthonormality and true positive active reference energies.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}


/-- The actual base image of the true canonical CG error is nonzero strictly before genuine active exhaustion.
Use: The actual base image of the true canonical CG error is nonzero strictly before genuine active exhaustion.
Article: main_krylov, apB:eq:Ahe and thm:select, actual final-error image norm.
Proof: Actual nonstagnation and genuine invertible metric give a real nonzero canonical error; the true positive base operator cannot annihilate it. -/
theorem canonical_final_error_image_ne_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    cgOperator base (cgCanonicalError base g k)≠0 := by
  -- Expand the genuine two-site norm before substituting the actual final-error image representation.
  have he : cgCanonicalError base g k≠0 := norm_pos_iff.mp
    (canonical_error_pos base hb _ (cg_nonstagnation base hb g k hk))
  intro hz
  have hp := (cgOperator_positive base hb).2 _ he
  rw [hz,inner_zero_right] at hp
  exact lt_irrefl _ hp

/-- The actual squared norm of the genuine final-error base image is its true residual norm fourth power times the two neighboring inverse step energies.
Use: The actual squared norm of the genuine final-error base image is its true residual norm fourth power times the two neighboring inverse step energies.
Article: main_krylov, apB:eq:Ahe and thm:select, actual final-error image norm.
Proof: The real neighboring normalized CG steps are genuinely orthonormal. Expand the actual two-site squared norm and cancel the true square-root energies on their proved positive domains. -/
theorem canonical_final_error_image_norm_sq (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k+1<referenceAtomCount base hb g) :
    ‖cgOperator base (cgCanonicalError base g (k+1))‖^2=
      ‖CG.gradient (cgOperator base) g (k+1)‖^4*((cgEnergy base g k)⁻¹+(cgEnergy base g (k+1))⁻¹) := by
  -- The actual active prefix gives genuine orthogonal neighboring unit steps and true positive energies.
  have hq := canonicalCGUnitStep_orthonormal base hb g (k+2)
    (fun i hi => cg_nonstagnation base hb g i (by omega))
  have hp : ‖canonicalCGUnitStep base g k‖=1 := hq.norm_eq_one ⟨k,by omega⟩
  have hn : ‖canonicalCGUnitStep base g (k+1)‖=1 := hq.norm_eq_one ⟨k+1,by omega⟩
  have ho : inner ℝ (canonicalCGUnitStep base g k) (canonicalCGUnitStep base g (k+1))=0 := by
    have hh := (orthonormal_iff_ite.mp hq) (⟨k,by omega⟩ : Fin (k+2)) ⟨k+1,by omega⟩
    simpa only [Fin.mk.injEq,show ¬ k=k+1 by omega,ite_false] using hh
  have hc := cgEnergy_pos base hb g k (by omega)
  have hd := cgEnergy_pos base hb g (k+1) hk
  have he : ‖(Real.sqrt (cgEnergy base g k))⁻¹ • canonicalCGUnitStep base g k-
      (Real.sqrt (cgEnergy base g (k+1)))⁻¹ • canonicalCGUnitStep base g (k+1)‖^2=
      (cgEnergy base g k)⁻¹+(cgEnergy base g (k+1))⁻¹ := by
    rw [norm_sub_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,hp,hn,mul_one,sq_abs,real_inner_smul_left,
      real_inner_smul_right,ho,mul_zero,sub_zero]
    rw [inv_pow,inv_pow,Real.sq_sqrt hc.le,Real.sq_sqrt hd.le]
  rw [canonical_final_error_image base hb g k hk,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,he]
  ring
end
end krylov.Envelope
