import krylov.Stability.WeightedNormalization
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, apB:lem:UAsteps, uniform exact line-step stability.
Use: compare true exact-search displacements with constants independent of
small reference direction lengths, including arbitrarily small CG energies.
Source: Cauchy--Schwarz, actual rank-one projection norms, a scalar reciprocal
estimate on [1/2,∞), and the proved weighted normalization bound.
-/

namespace krylov.Stability
noncomputable section
open krylov.Reference krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- An actual unit-direction curvature differs from one by at most the genuine operator deviation.
Use: The exact inverse search curvature is controlled independently of all step lengths.
Article: main_krylov, apB:lem:UAsteps.
Proof: Subtract the identity inside the real quadratic form and apply Cauchy--Schwarz and the actual operator norm. -/
theorem unit_curvature_error (B : E →L[ℝ] E) (u : E) (hu : ‖u‖=1) {η : ℝ}
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) : |inner ℝ u (B u)-1|≤η := by
  -- Retain the actual unit direction before applying the operator norm.
  have he : inner ℝ u (B u)-1=inner ℝ u ((B-ContinuousLinearMap.id ℝ E) u) := by
    change inner ℝ u (B u)-1=inner ℝ u (B u-u)
    rw [inner_sub_right,real_inner_self_eq_norm_sq,hu,one_pow]
  rw [he]
  have hi := norm_inner_le_norm (𝕜 := ℝ) u ((B-ContinuousLinearMap.id ℝ E) u)
  rw [Real.norm_eq_abs,hu,one_mul] at hi
  exact hi.trans (((B-ContinuousLinearMap.id ℝ E).le_opNorm u).trans (by simpa only [hu,mul_one] using hB))
/-- The real exact-search displacement in unit-direction rank-one form.
Use: Separate the actual gradient, normalized direction and genuine curvature denominator.
Article: main_krylov, apB:lem:UAsteps. -/
def unitLineUpdate (B : E →L[ℝ] E) (g u : E) : E :=
  -((inner ℝ u (B u))⁻¹ • (InnerProductSpace.rankOne ℝ u u) g)
/-- At the reference identity operator the actual unit-direction line step is the negative true rank-one projection.
Use: The real reference search is compared as a physical vector.
Article: main_krylov, apB:lem:UAsteps.
Proof: The true unit-vector curvature is one, so its actual inverse scalar cancels. -/
theorem unitLineUpdate_id (g u : E) (hu : ‖u‖=1) :
    unitLineUpdate (ContinuousLinearMap.id ℝ E) g u= -(InnerProductSpace.rankOne ℝ u u) g := by
  simp only [unitLineUpdate,ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,hu,one_pow,inv_one,one_smul]
/-- A true curvature at least one half has inverse at most two and linear reciprocal error.
Use: Supply explicit dimension-independent search denominator bounds.
Article: main_krylov, apB:lem:UAsteps.
Proof: Write the inverse error as (1−a)/a and use the actual positive lower curvature bound. -/
theorem curvature_reciprocal_bound (a : ℝ) (ha : (1/2 : ℝ)≤a) {η : ℝ} (h : |a-1|≤η) :
    |a⁻¹|≤2 ∧ |a⁻¹-1|≤2*η := by
  have hp : 0<a := by linarith
  have hi : a⁻¹≤2 := (inv_le_comm₀ hp (by norm_num)).mpr (by norm_num; exact ha)
  refine ⟨by rw [abs_of_pos (inv_pos.mpr hp)]; exact hi,?_⟩
  have he : a⁻¹-1=(1-a)*a⁻¹ := by field_simp
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hp),abs_sub_comm]
  exact (mul_le_mul h hi (inv_nonneg.mpr hp.le) (h.trans' (abs_nonneg _))).trans_eq (by ring)
/-- Actual unit-direction line updates obey a uniform bound in gradient, metric and weighted direction errors.
Use: No inverse physical step length enters the estimate.
Article: main_krylov, apB:lem:UAsteps.
Proof: Split the real displacement difference into gradient, reciprocal-curvature and rank-one projection errors; each term has its proved actual operator bound. -/
theorem unitLineUpdate_perturbation (B : E →L[ℝ] E) (g g₀ u u₀ : E) (hu : ‖u‖=1) (hu₀ : ‖u₀‖=1)
    {η : ℝ} (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) (hη : η≤(1/2 : ℝ)) :
    ‖unitLineUpdate B g u-unitLineUpdate (ContinuousLinearMap.id ℝ E) g₀ u₀‖≤
      2*‖g-g₀‖+2*η*‖g₀‖+2*‖u-u₀‖*‖g₀‖ := by
  -- Each error term is bounded before any reference direction is normalized.
  let a := inner ℝ u (B u)
  let P := InnerProductSpace.rankOne ℝ u u
  let P₀ := InnerProductSpace.rankOne ℝ u₀ u₀
  have hae : |a-1|≤η := unit_curvature_error B u hu hB
  have ha : (1/2 : ℝ)≤a := by linarith [(abs_le.mp hae).1]
  obtain ⟨hai,had⟩ := curvature_reciprocal_bound a ha hae
  have hPn : ‖P‖=1 := by simp only [P,InnerProductSpace.norm_rankOne,hu,mul_one]
  have hPP : ‖P-P₀‖≤2*‖u-u₀‖ := unit_rankOne_difference u u₀ hu hu₀
  have hP (v : E) : ‖P v‖≤‖v‖ := by simpa only [hPn,one_mul] using P.le_opNorm v
  have hs : unitLineUpdate B g u-unitLineUpdate (ContinuousLinearMap.id ℝ E) g₀ u₀=
      -(a⁻¹ • P (g-g₀))-(a⁻¹-1) • P g₀-(P-P₀) g₀ := by
    rw [unitLineUpdate_id g₀ u₀ hu₀]
    change -(a⁻¹ • P g)- -(P₀ g₀)=_
    simp only [map_sub,_root_.sub_apply,smul_sub,sub_smul,one_smul]
    module
  have h₁ : ‖-(a⁻¹ • P (g-g₀))‖≤2*‖g-g₀‖ := by
    rw [norm_neg,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hai (hP _) (norm_nonneg _) (by norm_num)
  have h₂ : ‖(a⁻¹-1) • P g₀‖≤2*η*‖g₀‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul had (hP _) (norm_nonneg _) (by linarith [abs_nonneg (a⁻¹-1)])
  have h₃ : ‖(P-P₀) g₀‖≤2*‖u-u₀‖*‖g₀‖ :=
    ((P-P₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right hPP (norm_nonneg _))
  rw [hs]
  exact ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
    (add_le_add (add_le_add h₁ h₂) h₃)

/-- The rank-one unit-direction update equals the actual implemented exact-search formula.
Use: Uniform estimates concern the genuine search displacement.
Article: main_krylov, apB:lem:UAsteps.
Proof: Expand the true rank-one action and rearrange its real scalar factors. -/
theorem unitLineUpdate_eq_line (B : E →L[ℝ] E) (g u : E) :
    unitLineUpdate B g u=lineLength g u (B u) • u := by
  simp only [unitLineUpdate,InnerProductSpace.rankOne_apply,lineLength,smul_smul,← neg_smul]
  congr 1
  ring
/-- The genuine exact-search displacement is invariant under nonzero rescaling of its actual direction.
Use: Pass between physical directions and actual normalized directions.
Article: main_krylov, apB:lem:UAsteps.
Proof: Cancel the nonzero directional scale in the actual search ratio; a zero true curvature is handled separately. -/
theorem lineStep_direction_scalar (B : E →L[ℝ] E) (g d : E) (c : ℝ) (hc : c≠0) :
    lineLength g (c • d) (B (c • d)) • (c • d)=lineLength g d (B d) • d := by
  simp only [lineLength,map_smul,real_inner_smul_right,real_inner_smul_left,smul_smul]
  congr 1
  by_cases hq : inner ℝ d (B d)=0
  · simp only [hq,mul_zero,div_zero,zero_mul]
  · field_simp

/-- Every actual nonzero-direction exact-search step has its genuine normalized rank-one representation.
Use: The uniform line-step bound applies to the real executed search.
Article: main_krylov, apB:lem:UAsteps.
Proof: Normalize by the real nonzero direction norm and apply exact directional rescaling invariance. -/
theorem lineStep_eq_unitLineUpdate (B : E →L[ℝ] E) (g d : E) (hd : d≠0) :
    lineLength g d (B d) • d=unitLineUpdate B g (NormedSpace.normalize d) := by
  rw [unitLineUpdate_eq_line]
  exact (lineStep_direction_scalar B g d _ (inv_ne_zero (norm_ne_zero_iff.mpr hd))).symm
/-- Weighted normalization gives a uniform exact-search stability bound without a smallest reference direction.
Use: This is the small-CG-energy line-step mechanism needed by the actual FC induction.
Article: main_krylov, apB:lem:UAsteps.
Proof: The true reference gradient is bounded by its actual reference direction; weighted normalization cancels that direction length before the unit-direction search estimate is applied. -/
theorem normalizedLineStep_stability (B : E →L[ℝ] E) (g g₀ d d₀ : E) (hd : d≠0) (hd₀ : d₀≠0)
    (hgd : ‖g₀‖≤‖d₀‖) {η : ℝ}
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) (hη : η≤(1/2 : ℝ)) :
    ‖unitLineUpdate B g (NormedSpace.normalize d)-
      unitLineUpdate (ContinuousLinearMap.id ℝ E) g₀ (NormedSpace.normalize d₀)‖≤
      2*‖g-g₀‖+2*η*‖g₀‖+4*‖d-d₀‖ := by
  -- The reference direction norm remains as a weight and cancels through the true gradient/direction ratio.
  have hu := NormedSpace.norm_normalize hd
  have hu₀ := NormedSpace.norm_normalize hd₀
  have hw := normalization_error_weight d (NormedSpace.normalize d₀) hd hu₀
    ‖d₀‖ ‖g₀‖ 1 ‖d-d₀‖ (norm_pos_iff.mpr hd₀) (by norm_num)
    (by simp only [NormedSpace.norm_smul_normalize,le_refl]) (by simpa only [one_mul] using hgd)
  have hb := unitLineUpdate_perturbation B g g₀ _ _ hu hu₀ hB hη
  exact hb.trans (by nlinarith)

/-- The genuine exact-search displacement has a uniform stability bound independent of a smallest reference step or direction.
Use: real FC canonical line steps inherit explicit perturbation constants even near CG exhaustion.
Article: main_krylov, apB:lem:UAsteps, uniform line-step comparison.
Proof: represent both actual exact searches by their true normalized rank-one updates and apply the proved weighted line-step estimate. -/
theorem lineStep_stability (B : E →L[ℝ] E) (g g₀ d d₀ : E) (hd : d≠0) (hd₀ : d₀≠0)
    (hgd : ‖g₀‖≤‖d₀‖) {η : ℝ}
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) (hη : η≤(1/2 : ℝ)) :
    ‖lineLength g d (B d) • d-lineLength g₀ d₀ d₀ • d₀‖≤
      2*‖g-g₀‖+2*η*‖g₀‖+4*‖d-d₀‖ := by
  rw [lineStep_eq_unitLineUpdate B g d hd]
  have hr := lineStep_eq_unitLineUpdate (ContinuousLinearMap.id ℝ E) g₀ d₀ hd₀
  rw [ContinuousLinearMap.id_apply] at hr
  rw [hr]
  exact normalizedLineStep_stability B g g₀ d d₀ hd hd₀ hgd hB hη

end
end krylov.Stability
