import krylov.Stability.WeightedOldProjection
import krylov.Stability.ProjectedDirectionBounds
import krylov.Stability.AnalyticFC
import krylov.Methods.DirectionReindex
import krylov.Methods.CanonicalWindows
import krylov.LinearAlgebra.SpectralConditioning

/-!
Article: main_krylov, apB:lem:UAsteps, actual canonical FC/CG direction geometry.
Use: discharge the real span, reference-projection, direction-size and
exact-search identifications used by the finite uniform FC stability induction.
Source: true positive metric roots, actual FC quadratic transcript equality,
proved genuine CG orthogonality and spectral quadratic-form bounds.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- Normalizing every true column preserves its actual real span, including zero columns and empty families.
Use: canonical old-span identities require no extra nonzero-column assumption.
Article: main_krylov, apB:lem:UAsteps.
Proof: normalized columns are scalar multiples of the real columns, while
each real column is its norm times its actual zero-safe normalization. -/
theorem span_normalize_eq_span {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ι → E) :
    Submodule.span ℝ (Set.range (fun i => NormedSpace.normalize (s i)))=Submodule.span ℝ (Set.range s) := by
  -- Zero-safe normalization preserves the real span in both directions.
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ ‖s i‖⁻¹ (Submodule.subset_span (Set.mem_range_self i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change s i∈Submodule.span ℝ (Set.range (fun i => NormedSpace.normalize (s i)))
    have hm := Submodule.smul_mem (Submodule.span ℝ (Set.range (fun i => NormedSpace.normalize (s i))))
        ‖s i‖ (Submodule.subset_span (Set.mem_range_self i))
    rw [NormedSpace.norm_smul_normalize] at hm
    exact hm

/-- The actual reference base sends the true inverse-root gradient to its genuine root gradient.
Use: the physical FC −g term becomes exactly −A times the true canonical gradient.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual positive base is its genuine root square; cancel the
proved nonsingular root inverse on the right before taking the vector action. -/
theorem canonical_base_dual (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    cgOperator base (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) g := by
  have he : base*(metricRoot base)⁻¹=metricRoot base := by
    calc
      _ = (metricRoot base*metricRoot base)*(metricRoot base)⁻¹ :=
        congrArg (fun M => M*(metricRoot base)⁻¹) (metricRoot_square base hb).symm
      _ = _ := by rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),Matrix.mul_one]
  change Matrix.toEuclideanCLM (𝕜 := ℝ) base (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)=_
  rw [← mul_apply_eq_comp,← map_mul,he]

/-- The actual canonical FC direction plus the genuine base-gradient term lies in the true span of the real normalized old steps.
Use: discharge the source projected-direction representation from the executed data-only coefficient solve, without a trajectory or direction expansion assumption.
Article: main_krylov, apB:lem:UAsteps.
Proof: normalize only the actual span, then transform the proved real
fixed-age FC coefficient formula through the genuine root. Each actual
synthesis summand is one of the real old canonical steps. -/
theorem fullFC_canonical_direction_span (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    R (fcDirection fullMemory A g k)+cgOperator base
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g k))∈
      Submodule.span ℝ (Set.range (fun i : Fin k => NormedSpace.normalize (R (fcStep fullMemory A g i.val)))) := by
  -- Transform the real coefficient synthesis before asserting actual old-span membership.
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  dsimp only
  rw [span_normalize_eq_span,canonical_base_dual base hb]
  have he : R (fcDirection fullMemory A g k)+R (fcGradient fullMemory A g k)=
      ∑ i : Fin k, conjugacyCoefficients
        (fun i : Fin k => fcStep fullMemory A g (k-1-i.val))
        (fun i : Fin k => fcSecant fullMemory A g (k-1-i.val)) (fcGradient fullMemory A g k) i •
          R (fcStep fullMemory A g (k-1-i.val)) := by
    rw [fullFC_direction_array]
    simp only [conjugacyDirection,combine,map_add,map_neg,map_sum,map_smul]
    abel
  rw [he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨k-1-i.val,by omega⟩,rfl⟩

/-- A genuine positive reference with eigenvalues at least one has a contractive actual inverse-root gradient map.
Use: derive the true reference gradient/direction weight in the uniform exact-search estimate.
Article: main_krylov, apB:lem:UAsteps, μ=1.
Proof: Parseval in the actual orthonormal eigenbasis and the genuine root
eigenvector formula compare each real squared dual coordinate with its
physical gradient coordinate using the true eigenvalue lower bound. -/
theorem canonical_dual_norm_le (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hlow : ∀ i, 1≤hb.1.eigenvalues i) (g : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤‖g‖ := by
  -- Compare genuine squared eigen-coordinates; only the actual spectral lower bound enters.
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← hb.1.eigenvectorBasis.repr.norm_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g),
    ← hb.1.eigenvectorBasis.repr.norm_map g,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  rw [OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply,gradient_spectral_coordinate base hb g i,
    mul_pow,Real.sq_sqrt (hb.posSemidef.eigenvalues_nonneg i)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hlow i)
    (sq_nonneg (inner ℝ (hb.1.eigenvectorBasis i) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)))

/-- The true CG canonical error norm is bounded by the actual canonical direction norm when the reference spectrum begins at one.
Use: remove every smallest-reference-direction denominator in the exact-line stability estimate.
Article: main_krylov, apB:lem:UAsteps, ‖D_k⁰‖≥‖e_k‖.
Proof: actual CG search pairing is the negative physical gradient energy.
The true canonical pairing and Cauchy--Schwarz bound that energy by the
canonical error times direction norm; genuine inverse-root contraction
then gives the claimed weight, including a stopped reference. -/
theorem canonicalCG_direction_size (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hlow : ∀ i, 1≤hb.1.eigenvalues i) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ i<k, CG.gradient (cgOperator base) g i≠0) :
    ‖cgCanonicalError base g k‖≤‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (CG.direction (cgOperator base) g k)‖ := by
  -- Keep the true canonical error as its own weight throughout the real search pairing argument.
  let r := CG.gradient (cgOperator base) g k
  let d := CG.direction (cgOperator base) g k
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  -- Transfer genuine physical conjugacy through the actual root before normalizing old steps.
  have hk := CG.invariant (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k hpre
  have he : inner ℝ (R d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ r)= -‖r‖^2 := by
    rw [← canonical_search_pairing base hb]
    exact hk.search_pair
  have hi := norm_inner_le_norm (𝕜 := ℝ) (R d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ r)
  rw [he,Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg _)] at hi
  have hlow := canonical_dual_norm_le base hb hlow r
  change ‖cgCanonicalError base g k‖≤‖r‖ at hlow
  change ‖r‖^2≤‖R d‖*‖cgCanonicalError base g k‖ at hi
  change ‖cgCanonicalError base g k‖≤‖R d‖
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hlow
  nlinarith [norm_nonneg (cgCanonicalError base g k),norm_nonneg (R d),norm_nonneg r]

/-- The true positive reference matrix eigenvalue upper bound controls its actual Euclidean operator norm.
Use: all induction constants use the genuine spectral conditioning parameter.
Article: main_krylov, apB:lem:UAsteps.
Proof: apply the existing spectral norm theorem to the actual positive base and its genuine nonnegative eigenvalues. -/
theorem cgOperator_norm_le (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {κ : ℝ} (hκ : 0≤κ) (hupp : ∀ i, hb.1.eigenvalues i≤κ) : ‖cgOperator base‖≤κ :=
  spectral_norm_le_of_eigenvalues base hb.1 hκ (fun i => ⟨hb.posSemidef.eigenvalues_nonneg i,hupp i⟩)

/-- The actual canonical CG direction plus its genuine base-error action belongs to the true normalized CG old-step span.
Use: the reference projected-direction equation follows from the real algorithm.
Article: main_krylov, apB:lem:UAsteps.
Proof: specialize the actual FC span equation to its true positive static
quadratic; proved executed FC/CG equality identifies every genuine old step,
current gradient and current direction. -/
theorem canonicalCG_direction_span (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    R (CG.direction (cgOperator base) g k)+cgOperator base (cgCanonicalError base g k)∈
      Submodule.span ℝ (Set.range (fun i : Fin k => canonicalCGUnitStep base g i.val)) := by
  -- Actual static FC transcript equality supplies every real reference column.
  have hp := cgOperator_positive base hb
  have hs := fullFC_canonical_direction_span base hb (fun _ => cgOperator base) g k
  dsimp only at hs ⊢
  rw [(fullFC_reference_step (cgOperator base) hp.1 hp.2 g k).1,
    (fullFC_reference_step (cgOperator base) hp.1 hp.2 g k).2.1] at hs
  have he : (fun i : Fin k => NormedSpace.normalize
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory (fun _ => cgOperator base) g i.val)))=
      fun i : Fin k => canonicalCGUnitStep base g i.val := by
    funext i
    rw [(fullFC_reference_step (cgOperator base) hp.1 hp.2 g i.val).2.2]
    rfl
  rw [he] at hs
  exact hs

/-- The actual canonical CG direction is orthogonal to every genuine earlier unit step.
Use: the reference old-span projection of the actual direction is exactly zero.
Article: main_krylov, apB:lem:UAsteps.
Proof: the real root pairing transfers true CG physical conjugacy to the
actual canonical steps; their genuine zero-safe normalization preserves the zero pairing. -/
theorem canonicalCG_direction_old_orth (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k, CG.gradient (cgOperator base) g i≠0)
    (j : Fin k) :
    inner ℝ (canonicalCGUnitStep base g j.val)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k))=0 := by
  have hk := CG.invariant (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k hpre
  have he := canonical_search_pairing base hb (cgStep base g j.val)
    (cgOperator base (CG.direction (cgOperator base) g k))
  rw [canonical_reference_action base hb] at he
  have hz : inner ℝ (canonicalCGStep base g j.val)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k))=0 := by
    rw [canonicalCGStep,← he,cgStep,real_inner_smul_left,hk.conjugate j.val k j.isLt le_rfl,mul_zero]
  simp only [canonicalCGUnitStep,NormedSpace.normalize,real_inner_smul_left,hz,mul_zero]

/-- The true canonical CG direction is exactly the complement of its genuine old-span projected base-error action.
Use: discharge the real reference direction formula in the uniform projected-search theorem.
Article: main_krylov, apB:lem:UAsteps.
Proof: genuine CG old-step orthonormality identifies the true projector
with its real frame sum; actual conjugacy makes the direction projection
zero. Apply the proved genuine span decomposition to the actual CG direction. -/
theorem canonicalCG_direction_projection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k, CG.gradient (cgOperator base) g i≠0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k)=
      -(cgOperator base (cgCanonicalError base g k)-
        observedProjection (fun i : Fin k => canonicalCGUnitStep base g i.val)
          (cgOperator base (cgCanonicalError base g k))) := by
  -- The real orthonormal old-step frame represents the actual old-span projector.
  let q : Fin k → EuclideanSpace ℝ (Fin n) := fun i => canonicalCGUnitStep base g i.val
  have hQ : crossGram q q=1 := by
    ext i j
    exact (orthonormal_iff_ite.mp (canonicalCGUnitStep_orthonormal base hb g k hpre)) i j
  have hz : observedProjection q
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k))=0 := by
    rw [observedProjection_eq_frameSum q hQ,observedFrameSum_apply]
    have hc : coordinates q
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k))=0 := by
      funext i
      exact canonicalCG_direction_old_orth base hb g k hpre i
    rw [hc]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  have hd := observedProjection_decomposition q (cgOperator base) (cgCanonicalError base g k)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k))
    (canonicalCG_direction_span base hb g k)
  rw [hz,add_zero] at hd
  exact hd

/-- Every actual nonstagnant CG search has a genuinely nonzero canonical direction.
Use: the true reference search normalization is defined before taking a uniform line bound.
Article: main_krylov, apB:lem:UAsteps.
Proof: the real CG positive-line theorem gives a nonzero physical direction;
the proved true inverse root cancels any hypothetical zero canonical image. -/
theorem canonicalCG_direction_ne (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k)≠0 := by
  have hp := cgOperator_positive base hb
  have hn := (CG.invariant_line_pos (cgOperator base) hp.2 g k
    (CG.invariant (cgOperator base) hp.1 hp.2 g k (fun i hi => hpre i hi.le)) (hpre k le_rfl)).1
  intro hz
  have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
  rw [canonical_primal_dual_cancel base hb,map_zero] at he
  exact hn he

/-- The true canonical CG step is exactly its actual identity-metric line-search update.
Use: compare the real FC line displacement with the genuine CG reference step.
Article: main_krylov, apB:lem:UAsteps.
Proof: actual root pairing preserves the real search scalar, and the true
static reference operator becomes identity in canonical primal/dual coordinates. -/
theorem canonicalCG_line_step (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let D := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k)
    lineLength (cgCanonicalError base g k) D D • D=canonicalCGStep base g k := by
  have hl := canonical_lineLength base hb (CG.gradient (cgOperator base) g k)
    (CG.direction (cgOperator base) g k) (cgOperator base (CG.direction (cgOperator base) g k))
  rw [canonical_reference_action base hb] at hl
  dsimp only
  rw [cgCanonicalError,hl]
  simp only [canonicalCGStep,cgStep,cgLine,map_smul]

/-- The actual canonical FC step is exactly its real canonical-operator line-search update.
Use: the uniform projected-search estimate applies to the genuine executed step.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual canonical operator and root pairing preserve both true
search numerator and curvature; linearity transports the real physical step. -/
theorem fullFC_canonical_line_step (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let D := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcDirection fullMemory A g k)
    lineLength (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g k))
      D (canonicalOperator base (A k) D) • D=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g k) := by
  dsimp only
  rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
  rw [fcStep,map_smul]
end
end krylov.Stability
