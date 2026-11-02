import krylov.Variation.ReferenceFlags
import krylov.LinearAlgebra.PlanarAggregation

/-!
Article: main_krylov, thm:A, sharp norm of the reference response operator.
Use: prove the spectral box constant and actual symmetric attaining increments
for the true computed CG flags and tails. Identifying this operator with the
derivative of the executed adaptive FC cycle is a separate trajectory theorem.
Source: contractive orthogonal projections and the actual planar attaining matrices.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The reference full-cycle response operator on actual canonical matrix increments.
Use: the candidate first variation uses the genuine computed reference flags and tails.
Article: main_krylov, thm:A, F(E)=ΣP_lE_lv_l. -/
def fullCycleResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (I : Finset ℕ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈I, (oldFlag base g l).starProjection
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l) (remainingTail base g l))

/-- The actual reference response obeys the spectral box-budget bound.
Use: gives the claimed first-order coefficient once the adaptive derivative is identified.
Article: main_krylov, thm:A, Σω_l‖e_(l+1)‖_A.
Proof: the genuine orthogonal flags are contractive; bound each actual operator
action and sum its true remaining-tail norm. Symmetry is not needed for this upper bound. -/
theorem spectral_response_le (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (I : Finset ℕ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ)
    (hω : ∀ l∈I, ‖E l‖≤ω l) :
    ‖fullCycleResponse base g I E‖≤∑ l∈I, ω l*‖cgCanonicalError base g (l+1)‖ := by
  apply (norm_sum_le I _).trans
  apply sum_le_sum
  intro l hl
  apply ((oldFlag base g l).norm_starProjection_apply_le _).trans
  have he := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E l)).le_opNorm (remainingTail base g l)
  rw [← Matrix.cstar_norm_def, remainingTail_norm] at he
  exact he.trans (mul_le_mul_of_nonneg_right (hω l hl) (norm_nonneg _))

/-- The actual planar cross increment has its budget, exact tail action and Frobenius energy.
Use: one physical construction will attain both the spectral box and Frobenius joint-budget constants.
Article: main_krylov, thm:A and prop:HS, E_l=b_l(q₀v̂_lᵀ+v̂_lq₀ᵀ).
Proof: actual CG orthogonality gives an orthonormal physical plane; apply the
proved planar norm and projection identities and rescale its actual nonzero tail. -/
theorem response_cross_increment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) (hl : l+1<referenceAtomCount base hb g)
    (b : ℝ) (hb' : 0≤b) :
    let e := canonicalCGUnitStep base g 0
    let v := remainingTail base g l
    let h := NormedSpace.normalize v
    let M := planarMatrix e h 0 b 0
    M.IsSymm ∧ ‖M‖≤b ∧ chebyshev1.hsSq M=2*b^2 ∧
      (oldFlag base g l).starProjection
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M v)=(b*‖v‖) • e := by
  -- The true reference tail is nonzero and orthogonal to the complete actual old flag.
  let e := canonicalCGUnitStep base g 0
  let v := remainingTail base g l
  let h := NormedSpace.normalize v
  have he : ‖e‖=1 := (firstStep_common base hb g (by omega)).1
  have hv : v≠0 := remainingTail_ne_zero base hb g l hl
  have hh : ‖h‖=1 := NormedSpace.norm_normalize hv
  have heK : e∈oldFlag base g l := unitStep_mem_oldFlag base g (Nat.zero_le l)
  have hhK : h∈(oldFlag base g l)ᗮ :=
    Submodule.smul_mem _ _ (remainingTail_orthogonal base hb g l (by omega))
  have heh : inner ℝ e h=0 := ((oldFlag base g l).mem_orthogonal h).mp hhK e heK
  refine ⟨planarMatrix_isSymm _ _ _ _ _, ?_, ?_, ?_⟩
  · have hn := planar_spectral_norm_le e h he hh heh 0 1 (by norm_num)
    have hs : planarMatrix e h 0 b 0=b • planarMatrix e h 0 1 0 := by
      simpa only [mul_zero, mul_one] using planarMatrix_scale e h b 0 1 0
    rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb']
    simpa only [chebyshev1.opNorm, neg_zero, mul_one] using mul_le_mul_of_nonneg_left hn hb'
  · simpa only [zero_pow (by omega : 2≠0), zero_add, add_zero] using planar_hsSq e h he hh heh 0 b 0
  · have hp := (projected_planar_actions (oldFlag base g l) e h he hh heh heK hhK 0 b 0 0).1
    have hvh : v=‖v‖ • h := (NormedSpace.norm_smul_normalize v).symm
    change (oldFlag base g l).starProjection
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h 0 b 0) v)=_
    conv_lhs => rw [hvh]
    rw [map_smul, map_smul, hp, smul_smul, mul_comm]

/-- Actual symmetric increments attain the complete spectral box response bound simultaneously.
Use: the sharp constant is attained for the true reference, with a common actual CG output direction.
Article: main_krylov, thm:A, explicit spectral attaining family.
Proof: choose each actual planar cross increment at its own budget; every
projected tail action points along the same true first CG unit step, so the triangle bound is exact. -/
theorem spectral_response_attained (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : 0<referenceAtomCount base hb g)
    (I : Finset ℕ) (hI : ∀ l∈I, l+1<referenceAtomCount base hb g)
    (ω : ℕ → ℝ) (hω : ∀ l∈I, 0≤ω l) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l∈I, (E l).IsSymm ∧ ‖E l‖≤ω l) ∧
      ‖fullCycleResponse base g I E‖=∑ l∈I, ω l*‖cgCanonicalError base g (l+1)‖ := by
  -- The construction uses the actual normalized remaining tail, not an arbitrary hidden direction.
  let e := canonicalCGUnitStep base g 0
  let E := fun l => planarMatrix e (NormedSpace.normalize (remainingTail base g l)) 0 (ω l) 0
  have hp (l : ℕ) (hl : l∈I) := response_cross_increment base hb g l (hI l hl) (ω l) (hω l hl)
  refine ⟨E,fun l hl => ⟨(hp l hl).1,(hp l hl).2.1⟩,?_⟩
  have hf : fullCycleResponse base g I E=
      (∑ l∈I, ω l*‖cgCanonicalError base g (l+1)‖) • e := by
    unfold fullCycleResponse
    rw [sum_smul]
    apply sum_congr rfl
    intro l hl
    simpa only [remainingTail_norm] using (hp l hl).2.2.2
  rw [hf, norm_smul, Real.norm_eq_abs, (firstStep_common base hb g hcount).1, mul_one,
    abs_of_nonneg (sum_nonneg fun l hl => mul_nonneg (hω l hl) (norm_nonneg _))]

/-- The sharp spectral reference response bound has exactly the printed Christoffel-profile form.
Use: every coefficient refers to the genuine initial-error spectral measure of the actual reference.
Article: main_krylov, thm:A, ‖F(E)‖/‖ê₀‖≤Σω_l√λ_(l+1).
Proof: substitute the true remaining-tail Christoffel identity into the
proved actual response bound and factor the actual initial error norm from the finite sum. -/
theorem spectral_response_christoffel (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (I : Finset ℕ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ) (hω : ∀ l∈I, ‖E l‖≤ω l) :
    ‖fullCycleResponse base g I E‖≤‖cgCanonicalError base g 0‖*
      ∑ l∈I, ω l*Real.sqrt (finiteChristoffelValue (energySpectralData base hb g hg) (l+1)) := by
  -- The already proved actual response norm is expressed through the true normalized spectral profile.
  apply (spectral_response_le base g I E ω hω).trans_eq
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  rw [← remainingTail_norm, remainingTail_christoffel base hb g hg]
  ring

end
end krylov.Variation
