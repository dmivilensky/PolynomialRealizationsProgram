import krylov.Envelope.CanonicalInjectionPairing
import krylov.Reference.Energy

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:Ahe and thm:select, genuine two-site final-error image.
Use: identify the actual base image of the true before-exhaustion error
in the genuine two neighboring CG unit-step coordinates.
Source: measured actual CG energy/line/residual identities, genuine
positive metric duality and the true CG direction recurrence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine metric-root image of every actual active CG direction equals its true normalized CG step times residual norm squared divided by square-root step energy.
Use: The genuine metric-root image of every actual active CG direction equals its true normalized CG step times residual norm squared divided by square-root step energy.
Article: main_krylov, apB:eq:Ahe and thm:select, genuine two-site final-error image.
Proof: Actual step energy is positive and equals the real line length times true squared residual norm. Normalize the genuine canonical step and cancel only the proved real nonzero line and energy factors. -/
theorem canonicalCG_direction_energy (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    cgOperator (metricRoot base) (CG.direction (cgOperator base) g k)=
      (‖CG.gradient (cgOperator base) g k‖^2/Real.sqrt (cgEnergy base g k)) • canonicalCGUnitStep base g k := by
  -- All divisions use genuine active CG energies and actual line lengths with their true nonzero domains.
  let c := cgEnergy base g k
  let a := CG.length (cgOperator base) g k
  have hs := canonicalCGStep_ne_zero base hb g k (fun i hi => cg_nonstagnation base hb g i (by omega))
  have hc : 0<c := by
    change 0<cgEnergy base g k
    rw [cgEnergy_eq_norm_sq base hb]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs)
  have ha : a≠0 := cgLine_ne_zero base g k hs
  have hroot : Real.sqrt c≠0 := (Real.sqrt_pos.mpr hc).ne'
  have henergy : c=a*‖CG.gradient (cgOperator base) g k‖^2 := cgEnergy_eq_length_norm base hb g hk
  have hcoef : Real.sqrt c/a=‖CG.gradient (cgOperator base) g k‖^2/Real.sqrt c := by
    field_simp
    nlinarith [Real.sq_sqrt hc.le]
  have hunit : Real.sqrt c • canonicalCGUnitStep base g k=
      a • cgOperator (metricRoot base) (CG.direction (cgOperator base) g k) := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).trans (by
      rw [canonicalCGStep,cgStep,map_smul]
      rfl)
  calc
    _ =a⁻¹ • (a • cgOperator (metricRoot base) (CG.direction (cgOperator base) g k)) := by
      rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
    _ =(Real.sqrt c/a) • canonicalCGUnitStep base g k := by rw [← hunit,smul_smul,div_eq_inv_mul]
    _ =_ := by rw [hcoef]

/-- The actual base image of the genuine final canonical error is the true squared residual norm times the difference of the two neighboring normalized CG steps divided by their real square-root energies.
Use: The actual base image of the genuine final canonical error is the true squared residual norm times the difference of the two neighboring normalized CG steps divided by their real square-root energies.
Article: main_krylov, apB:eq:Ahe and thm:select, genuine two-site final-error image.
Proof: Apply the genuine metric root to the actual CG direction recurrence, substitute the proved real direction energy normalizations and true residual-ratio beta, and use actual base/inverse-root metric duality. -/
theorem canonical_final_error_image (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k+1<referenceAtomCount base hb g) :
    cgOperator base (cgCanonicalError base g (k+1))=
      ‖CG.gradient (cgOperator base) g (k+1)‖^2 •
        ((Real.sqrt (cgEnergy base g k))⁻¹ • canonicalCGUnitStep base g k-
          (Real.sqrt (cgEnergy base g (k+1)))⁻¹ • canonicalCGUnitStep base g (k+1)) := by
  -- The actual CG direction recurrence gives the genuine neighboring-step representation of the true root-gradient image.
  have hrec := congrArg (cgOperator (metricRoot base)) (CG.direction_succ (cgOperator base) g k)
  rw [map_add,map_neg,map_smul,canonicalCG_direction_energy base hb g k (by omega),
    canonicalCG_direction_energy base hb g (k+1) hk] at hrec
  have hn : ‖CG.gradient (cgOperator base) g k‖^2≠0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g k (by omega)))
  have hcoef : CG.beta (cgOperator base) g k*(‖CG.gradient (cgOperator base) g k‖^2/Real.sqrt (cgEnergy base g k))=
      ‖CG.gradient (cgOperator base) g (k+1)‖^2/Real.sqrt (cgEnergy base g k) := by
    dsimp only [CG.beta]
    calc
      _ = (‖CG.gradient (cgOperator base) g (k+1)‖^2*(‖CG.gradient (cgOperator base) g k‖^2/‖CG.gradient (cgOperator base) g k‖^2))/Real.sqrt (cgEnergy base g k) := by ring
      _ = _ := by rw [div_self hn,mul_one]
  rw [smul_smul,hcoef] at hrec
  have he := canonical_base_dual base hb (CG.gradient (cgOperator base) g (k+1))
  change cgOperator base (cgCanonicalError base g (k+1))=cgOperator (metricRoot base) (CG.gradient (cgOperator base) g (k+1)) at he
  rw [he]
  rw [smul_sub,smul_smul,smul_smul,← div_eq_mul_inv,← div_eq_mul_inv]
  exact eq_sub_iff_add_eq.mpr (by rw [hrec];abel)
end
end krylov.Envelope
