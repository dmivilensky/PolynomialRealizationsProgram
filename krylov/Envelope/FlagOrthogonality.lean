import krylov.Envelope.AbsorbedCompression

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), true canonical absorbed-pairing geometry.
Use: prove real explored-flag inclusion, actual later-step orthogonality
and exact preservation of true complementary-flag pairings by genuine
absorbed increment compression.
Source: actual computed CG orthonormal prefixes and standard true finite
orthogonal projection identities.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine finite explored canonical CG flags increase with the actual prefix count.
Use: The genuine finite explored canonical CG flags increase with the actual prefix count.
Article: main_krylov, apB:lem:mu(b), true canonical absorbed-pairing geometry.
Proof: Embed each true finite step index into the genuine longer prefix. -/
theorem exploredFlag_mono (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    {r s : ℕ} (hrs : r≤s) : exploredFlag base g r≤exploredFlag base g s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact Submodule.subset_span ⟨(⟨i.val,i.isLt.trans_le hrs⟩ : Fin s),rfl⟩

/-- Every actual active canonical CG step is orthogonal to the genuine earlier explored flag.
Use: Every actual active canonical CG step is orthogonal to the genuine earlier explored flag.
Article: main_krylov, apB:lem:mu(b), true canonical absorbed-pairing geometry.
Proof: The actual normalized CG prefix is truly orthonormal; its genuine earlier generators pair to zero with the real later step, and linearity extends to their actual span. -/
theorem canonicalCGStep_later_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N r j : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (hrj : r≤j) (hj : j<N) : canonicalCGStep base g j∈(exploredFlag base g r)ᗮ := by
  -- Use the actual nonstagnating normalized CG prefix before extending true generator orthogonality to the genuine explored span.
  have hq := canonicalCGUnitStep_orthonormal base hb g N (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,rfl⟩ := hv
    have hi : i.val<N := i.isLt.trans_le (hrj.trans hj.le)
    have he := hq.inner_eq_zero (show (⟨i.val,hi⟩ : Fin N)≠⟨j,hj⟩ from by
      intro h
      have heval : i.val=j := by simpa only [Fin.val_mk] using congrArg Fin.val h
      omega)
    have hs : canonicalCGStep base g j=‖canonicalCGStep base g j‖ • canonicalCGUnitStep base g j :=
      (NormedSpace.norm_smul_normalize _).symm
    change inner ℝ (canonicalCGUnitStep base g i.val) (canonicalCGStep base g j)=0
    have he' : inner ℝ (canonicalCGUnitStep base g i.val) (canonicalCGUnitStep base g j)=0 := by
      simpa only [Fin.val_mk] using he
    rw [hs,inner_smul_right,he',mul_zero]
  | zero => exact inner_zero_left _
  | add u v _ _ hu hv => rw [inner_add_left,hu,hv,zero_add]
  | smul a v _ hv => rw [real_inner_smul_left,hv,mul_zero]

/-- Genuine complementary-flag test-vector pairings are unchanged by actual absorbed canonical increment compression.
Use: Genuine complementary-flag test-vector pairings are unchanged by actual absorbed canonical increment compression.
Article: main_krylov, apB:lem:mu(b), true canonical absorbed-pairing geometry.
Proof: Both real test vectors are fixed by the true complementary projector; move the actual symmetric projector across the genuine inner product. -/
theorem absorbedIncrements_pairing (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) (u v : EuclideanSpace ℝ (Fin n))
    (hu : u∈(exploredFlag base g (l+1))ᗮ) (hv : v∈(exploredFlag base g (l+1))ᗮ) :
    inner ℝ u (cgOperator (absorbedIncrements base g E l) v)=inner ℝ u (cgOperator (E l) v) := by
  rw [absorbedIncrements_operator]
  let P := (exploredFlag base g (l+1))ᗮ
  have hu' : P.starProjection u=u := Submodule.starProjection_eq_self_iff.mpr hu
  have hv' : P.starProjection v=v := Submodule.starProjection_eq_self_iff.mpr hv
  change inner ℝ u (P.starProjection (cgOperator (E l) (P.starProjection v)))=_
  rw [hv',← P.inner_starProjection_left_eq_right u,hu']
end
end krylov.Envelope
