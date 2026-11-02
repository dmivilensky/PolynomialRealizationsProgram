import krylov.Stability.UniformFCStep

/-!
Article: main_krylov, apB:lem:UAsteps, arbitrary positive spectral scale.
Use: normalize actual canonical search directions by the true lower spectral
endpoint inside the real stability estimate, retaining condition-ratio-only constants.
Source: true eigenbasis Parseval, actual CG search energy and exact invariance
of the real line displacement under nonzero direction rescaling.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine inverse-root error energy is bounded by physical gradient energy divided by the actual spectral lower endpoint.
Use: The genuine inverse-root error energy is bounded by physical gradient energy divided by the actual spectral lower endpoint.
Article: main_krylov, apB:lem:UAsteps.
Proof: Compare the actual squared eigen-coordinates using the genuine root spectral formula. -/
theorem canonical_dual_energy_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {μ : ℝ} (hlow : ∀ i, μ≤hb.1.eigenvalues i) (g : EuclideanSpace ℝ (Fin n)) :
    μ*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖^2≤‖g‖^2 := by
  -- The comparison uses actual eigen-coordinates, without changing the physical method.
  rw [← hb.1.eigenvectorBasis.repr.norm_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g),
    ← hb.1.eigenvectorBasis.repr.norm_map g,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply,gradient_spectral_coordinate base hb g i,
    mul_pow,Real.sq_sqrt (hb.posSemidef.eigenvalues_nonneg i)]
  exact mul_le_mul_of_nonneg_right (hlow i) (sq_nonneg _)

/-- The actual reference direction divided by the spectral lower endpoint dominates the true canonical error norm.
Use: The actual reference direction divided by the spectral lower endpoint dominates the true canonical error norm.
Article: main_krylov, apB:lem:UAsteps.
Proof: Combine the actual CG search pairing and Cauchy--Schwarz with the proved scaled dual-energy inequality. -/
theorem canonicalCG_scaled_direction_size (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {μ : ℝ} (hμ : 0<μ) (hlow : ∀ i, μ≤hb.1.eigenvalues i) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ i<k, CG.gradient (cgOperator base) g i≠0) :
    ‖cgCanonicalError base g k‖≤‖μ⁻¹ • (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (CG.direction (cgOperator base) g k))‖ := by
  -- Keep the true reference energy paired with its own real direction.
  let r := CG.gradient (cgOperator base) g k
  let d := CG.direction (cgOperator base) g k
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  have hk := CG.invariant (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k hpre
  have he : inner ℝ (R d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ r)= -‖r‖^2 := by
    rw [← canonical_search_pairing base hb]
    exact hk.search_pair
  have hi := norm_inner_le_norm (𝕜 := ℝ) (R d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ r)
  rw [he,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg _)] at hi
  have hlow := canonical_dual_energy_scale base hb hlow r
  change μ*‖cgCanonicalError base g k‖^2≤‖r‖^2 at hlow
  change ‖r‖^2≤‖R d‖*‖cgCanonicalError base g k‖ at hi
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hμ)]
  apply (le_inv_mul_iff₀ hμ).mpr
  nlinarith [norm_nonneg (cgCanonicalError base g k),norm_nonneg (R d)]

/-- The genuine base operator divided by its lower endpoint has norm at most its spectral condition bound.
Use: The genuine base operator divided by its lower endpoint has norm at most its spectral condition bound.
Article: main_krylov, apB:lem:UAsteps.
Proof: Use the true upper spectral bound and cancel the positive lower endpoint. -/
theorem scaled_base_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {μ κ : ℝ} (hμ : 0<μ) (hκ : 0≤κ) (hhigh : ∀ i, hb.1.eigenvalues i≤μ*κ) :
    ‖μ⁻¹ • cgOperator base‖≤κ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hμ)]
  exact (mul_le_mul_of_nonneg_left (cgOperator_norm_le base hb (mul_nonneg hμ.le hκ) hhigh)
    (inv_nonneg.mpr hμ.le)).trans_eq (by field_simp)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {p : ℕ}

/-- The real uniform observed-search estimate is unchanged after nonzero direction scaling and uses the scaled base norm.
Use: The real uniform observed-search estimate is unchanged after nonzero direction scaling and uses the scaled base norm.
Article: main_krylov, apB:lem:UAsteps.
Proof: Scale the actual old-span relation and true reference projection identity. Apply the proved real search theorem and cancel both actual line displacements by exact direction-scale invariance. -/
theorem observed_lineStep_stability_rescale (s y : Fin p → F) (H P₀ B : F →L[ℝ] F)
    (g g₀ d d₀ : F) (c : ℝ) (hc : c≠0)
    (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    (hd₀ : d₀= -(H g₀-P₀ (H g₀))) (hd : d≠0) (hd₀nz : d₀≠0) (hgd : ‖g₀‖≤‖c • d₀‖)
    {η ζ ε : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt p*η≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0)
    (hweight : ‖g₀‖*‖observedProjection s-P₀‖≤ε)
    (hB : ‖B-ContinuousLinearMap.id ℝ F‖≤ζ) (hζ : ζ≤1/2) :
    ‖lineLength g d (B d) • d-lineLength g₀ d₀ d₀ • d₀‖≤
      (2+8*‖c • H‖)*‖g-g₀‖+2*ζ*‖g₀‖+4*‖c • H‖*ε+64*Real.sqrt p*η*‖c • H‖*‖g‖ := by
  -- Scale the genuine span relation; exact search then removes the auxiliary direction scale.
  have hsp : c • d+(c • H) g∈Submodule.span ℝ (Set.range s) := by
    simpa only [_root_.smul_apply,smul_add] using (Submodule.span ℝ (Set.range s)).smul_mem c hspan
  have href : c • d₀= -((c • H) g₀-P₀ ((c • H) g₀)) := by
    rw [hd₀]
    simp only [_root_.smul_apply,map_smul,smul_neg,smul_sub]
  have h := observed_lineStep_stability s y (c • H) P₀ B g g₀ (c • d) (c • d₀) hs hG hsp href
    (smul_ne_zero hc hd) (smul_ne_zero hc hd₀nz) hgd hη hsmall hy
    (fun i => by rw [real_inner_smul_right,ho i,mul_zero]) hweight hB hζ
  rw [lineStep_direction_scalar B g d c hc] at h
  have hr : lineLength g₀ (c • d₀) (c • d₀) • (c • d₀)=lineLength g₀ d₀ d₀ • d₀ := by
    simpa only [ContinuousLinearMap.id_apply] using lineStep_direction_scalar (ContinuousLinearMap.id ℝ F) g₀ d₀ c hc
  rw [hr] at h
  exact h
end
end krylov.Stability
