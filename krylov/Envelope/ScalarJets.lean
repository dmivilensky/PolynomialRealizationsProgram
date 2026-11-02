import krylov.Envelope.JetSubspace

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual scalar-product first-jet recovery.
Use: preserve observed-vector jet coherence under genuine scalar decisions
and recover true probe jets from an actual nonzero reference line scalar.
Source: actual reference-flag linearity and the genuine scalar-vector product
rule, including the real coefficient-derivative vertical term.
-/

namespace krylov.Envelope
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine scalar-vector product jet preserves actual observed jet coherence.
Use: The genuine scalar-vector product jet preserves actual observed jet coherence.
Article: main_krylov, apB:lem:filtration, actual scalar-product first-jet recovery.
Proof: Add the true scalar multiple of the observation jet and its genuine coefficient-derivative vertical jet. -/
theorem jetSubspace_smul (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    {v dv : E} (hv : (v,dv)∈jetSubspace K L) (c dc : ℝ) :
    ((c • v,c • dv+dc • v) : E × E)∈jetSubspace K L := by
  have hj := (jetSubspace K L).add_mem ((jetSubspace K L).smul_mem c hv)
    ((jetSubspace K L).smul_mem dc (jetSubspace_vertical K L hv.1))
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero] using hj

/-- A true nonzero reference scalar allows recovery of genuine observed-vector jet coherence from its actual product jet.
Use: A true nonzero reference scalar allows recovery of genuine observed-vector jet coherence from its actual product jet.
Article: main_krylov, apB:lem:filtration, actual scalar-product first-jet recovery.
Proof: Recover actual reference-flag membership by scaling, subtract the real vertical coefficient jet and divide by the genuine nonzero scalar. -/
theorem jetSubspace_of_smul (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    {v dv : E} {c dc : ℝ} (hc : c≠0)
    (hv : ((c • v,c • dv+dc • v) : E × E)∈jetSubspace K L) :
    (v,dv)∈jetSubspace K L := by
  -- Recover the real reference vector before subtracting its actual coefficient-derivative vertical jet.
  have hvK : v∈K := by
    have h := K.smul_mem c⁻¹ hv.1
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h
  have h := (jetSubspace K L).sub_mem hv ((jetSubspace K L).smul_mem dc (jetSubspace_vertical K L hvK))
  have he : ((c • v,c • dv+dc • v) : E × E)-dc • (0,v)=c • (v,dv) := by
    ext <;> simp
  rw [he] at h
  have h' := (jetSubspace K L).smul_mem c⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h'

/-- Genuine current and post-search gradient jets determine the true probe jet whenever the actual reference search scalar is nonzero.
Use: Recover the real probe observation from the actual exact-search update.
Article: main_krylov, apB:lem:filtration, actual scalar-product first-jet recovery.
Proof: Subtract the genuine current-gradient jet from its actual post-search jet and apply the proved nonzero scalar-product recovery. -/
theorem jetSubspace_probe (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    {g dg z dz : E} {a da : ℝ} (ha : a≠0)
    (hg : (g,dg)∈jetSubspace K L)
    (hpost : (g+a • z,dg+(a • dz+da • z))∈jetSubspace K L) :
    (z,dz)∈jetSubspace K L := by
  apply jetSubspace_of_smul K L (dc := da) ha
  simpa only [Prod.mk_sub_mk,add_sub_cancel_left] using (jetSubspace K L).sub_mem hpost hg

/-- A real line-search displacement followed by a genuine zero-reference correction preserves the true observed step-jet flag.
Use: Propagate the actual total recorded physical step rather than only the search direction.
Article: main_krylov, apB:lem:filtration, actual scalar-product first-jet recovery.
Proof: Add the actual scalar-vector direction jet and the genuine vertical correction derivative in the real reference flag. -/
theorem jetSubspace_line_correction (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    {d dd χ : E} (hd : (d,dd)∈jetSubspace K L) (hχ : χ∈K) (a da : ℝ) :
    (a • d,a • dd+da • d+χ)∈jetSubspace K L := by
  convert (jetSubspace K L).add_mem (jetSubspace_smul K L hd a da)
    (jetSubspace_vertical K L hχ) using 1; ext <;> simp
end
end krylov.Envelope
