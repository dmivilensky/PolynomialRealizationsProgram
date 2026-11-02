import krylov.Design.SechAGMDuplication

/-!
Article: main_krylov, apC:lem:poisson, the complete actual elliptic nome reformulation.
Use: construct a genuine real modulus k in (0,1), prove the complete integral
K(k)=pi*(1+2*sum sech)/2 and its actual complementary integral, then identify
the standard nome exp(-pi*K(k')/K(k)) with exp(-theta).
Source: actual hyperbolic AGM duplication, the original Landen integral proof,
and genuine ordinary/half-lattice Poisson summation. See NIST DLMF 19.8 and 20.9.
-/

namespace krylov.Design
noncomputable section
open Real Filter Set jacobi.Young chebyshev1.SineJacobi

/-- The actual ordinary integer sech mass has the genuine complementary-spacing Poisson law.
Article: main_krylov, apC:lem:poisson. -/
theorem latticeSechMass_poisson {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass θ = π / θ * latticeSechMass (π ^ 2 / θ) := by
  have hdual : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  rw [latticeSechMass_eq hθ, latticeSechMass_eq hdual, poisson_sech hθ]
  rw [show π / (2 * θ) = (π / θ) / 2 by ring]
  ring

/-- The genuine hyperbolic masses obey the exact complementary quadratic identity.
Article: main_krylov, apC:lem:poisson, the real elliptic modulus dictionary. -/
theorem latticeSechMass_complementary_square {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass θ ^ 2 = latticeSechAlternatingMass θ ^ 2 + latticeSechHalfMass θ ^ 2 := by
  have hh : 0 < θ / 2 := div_pos hθ (by norm_num)
  have ha := latticeSechMass_duplication hh
  have hb := latticeSechAlternatingMass_duplication_sq hh
  have hc := latticeSechMass_sub_alternating hh
  rw [show 2 * (θ / 2) = θ by ring] at ha hb hc
  have hasq := congrArg (fun x : ℝ => x ^ 2) ha
  have hcsq := congrArg (fun x : ℝ => x ^ 2) hc
  nlinarith [hasq, hcsq]

/-- The actual hyperbolic modulus is the true positive half-lattice/ordinary mass ratio.
Article: main_krylov, apC:lem:poisson, the complementary period parameter. -/
theorem sechModulus_eq_half_ratio {θ : ℝ} (hθ : 0 < θ) :
    sechModulus θ = latticeSechHalfMass θ / latticeSechMass θ := by
  have hd := latticeSechMass_strict_domain hθ
  have hA : 0 < latticeSechMass θ := hd.1.trans hd.2
  have hC := latticeSechHalfMass_pos hθ
  have hs := latticeSechMass_complementary_square hθ
  have he : 1 - (latticeSechAlternatingMass θ / latticeSechMass θ) ^ 2 =
      (latticeSechHalfMass θ / latticeSechMass θ) ^ 2 := by
    field_simp [hA.ne']
    nlinarith
  rw [sechModulus, he, Real.sqrt_sq (div_pos hC hA).le]

/-- The actual hyperbolic modulus is the genuine alternating/ordinary ratio at complementary spacing.
Article: main_krylov, apC:lem:poisson, the elliptic nome dictionary. -/
theorem sechModulus_eq_dual_ratio {θ : ℝ} (hθ : 0 < θ) :
    sechModulus θ = latticeSechAlternatingMass (π ^ 2 / θ) / latticeSechMass (π ^ 2 / θ) := by
  have hdual : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  have hd := latticeSechMass_strict_domain hdual
  rw [sechModulus_eq_half_ratio hθ, poisson_sech_half hθ, latticeSechMass_poisson hθ]
  field_simp [hθ.ne', Real.pi_ne_zero, (hd.1.trans hd.2).ne']

/-- The true complementary modulus is the genuine hyperbolic modulus at reciprocal spacing.
Article: main_krylov, apC:lem:poisson, the real complementary K correspondence. -/
theorem sechModulus_complement_eq_dual {θ : ℝ} (hθ : 0 < θ) :
    sqrt (1 - sechModulus θ ^ 2) = sechModulus (π ^ 2 / θ) := by
  have hdual : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  rw [sechModulus_complement hθ]
  have h := sechModulus_eq_dual_ratio hdual
  rw [show π ^ 2 / (π ^ 2 / θ) = θ by field_simp] at h
  exact h.symm

/-- The actual complementary complete elliptic integral has its exact hyperbolic period.
Article: main_krylov, apC:lem:poisson, the substantive nome identification. -/
theorem ellipticK_sechModulus_complement {θ : ℝ} (hθ : 0 < θ) :
    ellipticK (sqrt (1 - sechModulus θ ^ 2)) = θ / 2 * latticeSechMass θ := by
  have hdual : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  rw [sechModulus_complement_eq_dual hθ, ellipticK_sechModulus hdual]
  have ha : latticeSechMass (π ^ 2 / θ) = θ / π * latticeSechMass θ := by
    rw [latticeSechMass_poisson hθ]
    field_simp [hθ.ne', Real.pi_ne_zero]
  rw [ha]
  field_simp [Real.pi_ne_zero]

/-- The standard elliptic nome, using the actual complete integral and actual complementary modulus.
Article: main_krylov, apC:lem:poisson; NIST DLMF https://dlmf.nist.gov/20.9.E5. -/
def ellipticNome (k : ℝ) : ℝ :=
  exp (-π * ellipticK (sqrt (1 - k ^ 2)) / ellipticK k)

/-- The standard genuine elliptic nome of the constructed modulus is exactly exp(-theta).
Article: main_krylov, apC:lem:poisson.
Both actual complete integrals are evaluated by their independently proved
hyperbolic period identities; this is not a definition of K or of the nome. -/
theorem ellipticNome_sechModulus {θ : ℝ} (hθ : 0 < θ) :
    ellipticNome (sechModulus θ) = exp (-θ) := by
  rw [ellipticNome, ellipticK_sechModulus_complement hθ, ellipticK_sechModulus hθ]
  congr 1
  have hd := latticeSechMass_strict_domain hθ
  field_simp [Real.pi_ne_zero, (hd.1.trans hd.2).ne']

/-- The source's exact elliptic-integral reformulation holds at a genuine real modulus with the stated standard nome.
Article: main_krylov, apC:lem:poisson, the complete `equivalently` assertion. -/
theorem sampledSech_elliptic_nome {θ : ℝ} (hθ : 0 < θ) :
    sechModulus θ ∈ Ioo 0 1 ∧ ellipticNome (sechModulus θ) = exp (-θ) ∧
      sampledSech θ = ellipticK (sechModulus θ) / π - 1 / 2 := by
  refine ⟨sechModulus_mem hθ, ellipticNome_sechModulus hθ, ?_⟩
  rw [ellipticK_sechModulus hθ, latticeSechMass_eq hθ]
  field_simp [Real.pi_ne_zero]
  ring

end
end krylov.Design
