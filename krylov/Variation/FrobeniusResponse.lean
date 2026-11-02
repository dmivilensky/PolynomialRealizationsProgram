import krylov.Variation.SpectralResponse

/-!
Article: main_krylov, prop:HS, sharp Hilbert--Schmidt reference response.
Use: instantiate the actual symmetric cross-block cost with the actual CG
tails, aggregate in the joint square budget, and construct an attaining family.
Source: symmetric off-diagonal blocks pay twice in Frobenius energy and finite Cauchy--Schwarz.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.LinearAlgebra chebyshev1
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An actual reference tail cross action pays the sharp √2 Frobenius cost.
Use: preserves the symmetric cross-block improvement before aggregating across increments.
Article: main_krylov, prop:HS.
Proof: normalize the genuine nonzero tail, use its proved actual flag
orthogonality and the existing sharp Hilbert--Schmidt compression estimate, then rescale. -/
theorem response_hs_cross (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) (hl : l+1<referenceAtomCount base hb g)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    Real.sqrt 2*‖(oldFlag base g l).starProjection
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M (remainingTail base g l))‖≤
      hsNorm M*‖remainingTail base g l‖ := by
  -- Rescale the actual unit-tail compression estimate by its genuine tail length.
  let v := remainingTail base g l
  let h := NormedSpace.normalize v
  have hv : v≠0 := remainingTail_ne_zero base hb g l hl
  have hh : h∈(oldFlag base g l)ᗮ :=
    Submodule.smul_mem _ _ (remainingTail_orthogonal base hb g l (by omega))
  have he := hs_cross_norm M hM (oldFlag base g l) h hh (NormedSpace.norm_normalize hv) (le_refl (hsNorm M))
  have hs : v=‖v‖ • h := (NormedSpace.norm_smul_normalize v).symm
  change Real.sqrt 2*‖(oldFlag base g l).starProjection
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M v)‖≤_
  conv_lhs => rw [hs]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
  calc
    _ = (Real.sqrt 2*‖(oldFlag base g l).starProjection
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M h)‖)*‖v‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (norm_nonneg v)

/-- The actual reference response obeys the sharp joint Hilbert--Schmidt upper bound.
Use: the coefficient depends on the entire true remaining-error profile rather than a triangle loss in the budgets.
Article: main_krylov, prop:HS, (ω/√2)√Σ‖e_(l+1)‖_A².
Proof: sum the actual √2 cross-action costs, apply finite Cauchy--Schwarz,
and insert the given joint squared Frobenius budget before taking nonnegative square roots. -/
theorem frobenius_response_le (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (I : Finset ℕ)
    (hI : ∀ l∈I, l+1<referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l∈I, (E l).IsSymm)
    (ω : ℝ) (hω : 0≤ω) (hbudget : ∑ l∈I, hsSq (E l)≤ω^2) :
    Real.sqrt 2*‖fullCycleResponse base g I E‖≤
      ω*Real.sqrt (∑ l∈I, ‖cgCanonicalError base g (l+1)‖^2) := by
  -- Cauchy--Schwarz couples the actual per-increment Frobenius costs to the true reference tail profile.
  have ht : Real.sqrt 2*‖fullCycleResponse base g I E‖≤∑ l∈I, hsNorm (E l)*‖remainingTail base g l‖ := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le I _) (Real.sqrt_nonneg 2)).trans
    rw [mul_sum]
    exact sum_le_sum fun l hl => response_hs_cross base hb g l (hI l hl) (E l) (hE l hl)
  have hc := sum_mul_sq_le_sq_mul_sq I (fun l => hsNorm (E l)) (fun l => ‖remainingTail base g l‖)
  simp only [hsNorm_sq, remainingTail_norm] at hc ht
  have hv : 0≤∑ l∈I, ‖cgCanonicalError base g (l+1)‖^2 := sum_nonneg fun _ _ => sq_nonneg _
  have hb := mul_le_mul_of_nonneg_right hbudget hv
  have hroot := Real.sq_sqrt hv
  apply ht.trans
  apply (sq_le_sq₀ (sum_nonneg fun _ _ => mul_nonneg (hsNorm_nonneg _) (norm_nonneg _))
    (mul_nonneg hω (Real.sqrt_nonneg _))).mp
  rw [mul_pow, hroot]
  exact hc.trans hb

/-- The true remaining-error square profile is positive for a nonempty preterminal increment set.
Use: normalize the exact Hilbert--Schmidt attaining allocation without a smallest-step hypothesis.
Article: main_krylov, prop:HS, attaining coefficient denominator.
Proof: one actual preterminal tail is nonzero and its strictly positive square
is at most the complete nonnegative finite profile sum. -/
theorem tailProfile_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (I : Finset ℕ) (hI : I.Nonempty)
    (hpre : ∀ l∈I, l+1<referenceAtomCount base hb g) :
    0<∑ l∈I, ‖remainingTail base g l‖^2 := by
  obtain ⟨l,hl⟩ := hI
  exact (sq_pos_of_pos (norm_pos_iff.mpr (remainingTail_ne_zero base hb g l (hpre l hl)))).trans_le
    (single_le_sum (f := fun j : ℕ => ‖remainingTail base g j‖^2) (fun _ _ => sq_nonneg _) hl)

/-- Actual symmetric increments attain the joint Hilbert--Schmidt reference response constant.
Use: supplies the source's physical attaining allocation for each true CG reference.
Article: main_krylov, prop:HS, E_l proportional to q₀v_lᵀ+v_lq₀ᵀ.
Proof: allocate each planar cross coefficient proportionally to its actual tail
norm; its twice-counted Frobenius squares exhaust the budget and all output actions add along q₀. -/
theorem frobenius_response_attained (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : 0<referenceAtomCount base hb g)
    (I : Finset ℕ) (hI : I.Nonempty) (hpre : ∀ l∈I, l+1<referenceAtomCount base hb g)
    (ω : ℝ) (hω : 0≤ω) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l∈I, (E l).IsSymm) ∧ (∑ l∈I, hsSq (E l))=ω^2 ∧
      ‖fullCycleResponse base g I E‖=
        (ω/Real.sqrt 2)*Real.sqrt (∑ l∈I, ‖cgCanonicalError base g (l+1)‖^2) := by
  -- Use the true tail-energy profile as the attaining allocation denominator.
  let V := Real.sqrt (∑ l∈I, ‖remainingTail base g l‖^2)
  have hV : 0<V := Real.sqrt_pos.mpr (tailProfile_pos base hb g I hI hpre)
  have hV2 : V^2=∑ l∈I, ‖remainingTail base g l‖^2 := Real.sq_sqrt (le_of_lt (tailProfile_pos base hb g I hI hpre))
  have hr : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : (Real.sqrt 2)^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  let b := fun l => (ω/(Real.sqrt 2*V))*‖remainingTail base g l‖
  have hb' (l : ℕ) : 0≤b l := mul_nonneg (div_nonneg hω (mul_pos hr hV).le) (norm_nonneg _)
  let e := canonicalCGUnitStep base g 0
  let E := fun l => planarMatrix e (NormedSpace.normalize (remainingTail base g l)) 0 (b l) 0
  have hp (l : ℕ) (hl : l∈I) := response_cross_increment base hb g l (hpre l hl) (b l) (hb' l)
  have hsum : (∑ l∈I, b l*‖remainingTail base g l‖)=(ω/Real.sqrt 2)*V := by
    simp only [b]
    simp_rw [mul_assoc, ← pow_two]
    rw [← mul_sum, ← hV2]
    field_simp
  refine ⟨E,fun l hl => (hp l hl).1,?_,?_⟩
  · calc
      _ = ∑ l∈I, 2*(b l)^2 := sum_congr rfl fun l hl => (hp l hl).2.2.1
      _ = (2*(ω/(Real.sqrt 2*V))^2)*(∑ l∈I, ‖remainingTail base g l‖^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro l _
        simp only [b, mul_pow]
        ring
      _ = ω^2 := by rw [← hV2, div_pow, mul_pow, hr2]; field_simp
  · have hf : fullCycleResponse base g I E=((ω/Real.sqrt 2)*V) • e := by
      unfold fullCycleResponse
      rw [← hsum, sum_smul]
      exact sum_congr rfl fun l hl => (hp l hl).2.2.2
    rw [hf, norm_smul, Real.norm_eq_abs, (firstStep_common base hb g hcount).1, mul_one,
      abs_of_nonneg (mul_nonneg (div_nonneg hω hr.le) hV.le)]
    simp only [V, remainingTail_norm]

end
end krylov.Variation
