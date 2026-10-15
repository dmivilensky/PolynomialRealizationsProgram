import «2610.05164v2».GroundState.Variational
import «2610.05164v2».GroundState.Convolution

/-!
Article: 2610.05164v2, Theorem 3.1.
The article's nonnegative normalized Rayleigh maximizer exists for every nonnegative integrable
density of positive mass, on the actual kernel operator.
Use: `«2610.05164v2».GroundState.exists_nonnegative_maximizer` feeds
`«2610.05164v2».GroundState.exists_regular_positive_ground` (Classical and Sobolev regularity of the
ground state, for general L1 density: no continuity or boundedness of m is assumed).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/--
Defines `absoluteLp` of type `FeatureSpace` by `(Lp.memLp f).norm.toLp (fun x => ‖f x‖)`.

Use: `«2610.05164v2».GroundState.absoluteLp_coe` uses this definition to establish the stated
quantitative bound `absoluteLp f =ᵐ[volume] (fun x => |f x|)`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.
-/
def absoluteLp (f : FeatureSpace) : FeatureSpace :=
  (Lp.memLp f).norm.toLp (fun x => ‖f x‖)

/--
The stated quantitative bound `absoluteLp f =ᵐ[volume] (fun x => |f x|)`.

Use: `«2610.05164v2».GroundState.absoluteLp_norm` uses this identity to establish exact
identity `‖absoluteLp f‖=‖f‖`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem absoluteLp_coe (f : FeatureSpace) : absoluteLp f =ᵐ[volume] (fun x => |f x|) := by
  have h : absoluteLp f =ᵐ[volume] (fun x => ‖f x‖) := (Lp.memLp f).norm.coeFn_toLp
  simpa only [Real.norm_eq_abs] using h

/--
Exact identity `‖absoluteLp f‖=‖f‖`.

Use: `«2610.05164v2».GroundState.exists_nonnegative_maximizer` uses this identity to establish
constructs witnesses with the exact properties `∃ f : FeatureSpace, ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem absoluteLp_norm (f : FeatureSpace) : ‖absoluteLp f‖=‖f‖ := by
  have he : ‖absoluteLp f‖^2=‖f‖^2 := by
    rw [l2_norm_sq, l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [absoluteLp_coe f] with x hx
    rw [hx,sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, |kernelOperator hm hn f
x| ≤ kernelOperator hm hn (absoluteLp f) x`.

Use: `«2610.05164v2».GroundState.kernel_absolute_quadratic` uses this bound to establish the
stated quantitative bound `inner ℝ f (kernelOperator hm hn f) ≤ inner ℝ (absoluteLp f)
(kernelOperator hm hn (absoluteLp f))`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem kernel_absolute_domination {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : ∀ᵐ x,
      |kernelOperator hm hn f x| ≤ kernelOperator hm hn (absoluteLp f) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [kernelOperator_coe hm hn f, kernelOperator_coe hm hn (absoluteLp f)] with x hx hy
  rw [hx,hy,abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg (m x))
  have he : (fun y => |exp (-|x-y|)*(sqrt (m y)*f y)|) =ᵐ[volume]
      (fun y => exp (-|x-y|)*sqrt (m y)*absoluteLp f y) := by
    filter_upwards [absoluteLp_coe f] with y hy
    rw [hy]
    simp only [abs_mul, abs_of_pos (exp_pos _), abs_of_nonneg (sqrt_nonneg _), mul_assoc]
  have h := norm_integral_le_integral_norm (μ := volume) (f := fun y => exp (-|x-y|)*(sqrt (m y)*f y))
  simp only [Real.norm_eq_abs] at h
  rw [integral_congr_ae he] at h
  have he' : (fun y => exp (-|x-y|)*sqrt (m y)*f y)=
      (fun y => exp (-|x-y|)*(sqrt (m y)*f y)) := by funext y; ring
  simpa only [he'] using h

/--
The stated quantitative bound `inner ℝ f (kernelOperator hm hn f) ≤ inner ℝ (absoluteLp f)
(kernelOperator hm hn (absoluteLp f))`.

Use: `«2610.05164v2».GroundState.exists_nonnegative_maximizer` uses this bound to establish
constructs witnesses with the exact properties `∃ f : FeatureSpace, ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem kernel_absolute_quadratic {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (f : FeatureSpace) : inner ℝ f (kernelOperator hm hn f) ≤
      inner ℝ (absoluteLp f) (kernelOperator hm hn (absoluteLp f)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [L2.inner_def,L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) f (kernelOperator hm hn f))
    (L2.integrable_inner (𝕜 := ℝ) (absoluteLp f) (kernelOperator hm hn (absoluteLp f)))
  filter_upwards [absoluteLp_coe f,kernel_absolute_domination hm hn f] with x hx hb
  change kernelOperator hm hn f x*f x ≤ kernelOperator hm hn (absoluteLp f) x*absoluteLp f x
  rw [hx]
  calc
    _ ≤ |kernelOperator hm hn f x*f x| := le_abs_self _
    _ = |kernelOperator hm hn f x| * |f x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/--
The article's nonnegative normalized Rayleigh maximizer exists for every nonnegative integrable
density of positive mass, on the actual kernel operator.

Constructs witnesses with the exact properties `∃ f : FeatureSpace, ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f`.

Use: `«2610.05164v2».GroundState.exists_positive_ground_eigenfunction` uses this identity to
establish constructs witnesses with the exact properties `∃ u : H1, (∀ x, 0 < H1.rep u x) ∧
densityOperator m u=kernelEigenvalue hm hn 0 • u`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem exists_nonnegative_maximizer {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ f : FeatureSpace,
      ‖f‖=1 ∧ (∀ᵐ x, 0 ≤ f x) ∧
      kernelOperator hm hn f=kernelEigenvalue hm hn 0 • f := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let D := kernelSpectralData hm hn
  have htrace : (∑' i, D.eig i)=∫ x, m x := by
    rw [← D.eigenvalue_tsum]
    exact kernelEigenvalue_mass hm hn
  obtain ⟨_,f,hf,he⟩ := D.top_attained (htrace ▸ hM)
  have hq : inner ℝ f (kernelOperator hm hn f)=D.eigenvalue 0 := by
    rw [he,real_inner_smul_right,real_inner_self_eq_norm_sq,hf]
    simp
  have ha := absoluteLp_norm f
  have hb := D.top_quadratic_bound (absoluteLp f)
  rw [ha,hf] at hb
  simp only [one_pow,mul_one] at hb
  have hl : D.eigenvalue 0 ≤ inner ℝ (absoluteLp f) (kernelOperator hm hn (absoluteLp f)) := by
    rw [← hq]
    exact kernel_absolute_quadratic hm hn f
  refine ⟨absoluteLp f,ha.trans hf,?_,?_⟩
  · filter_upwards [absoluteLp_coe f] with x hx
    rw [hx]
    exact abs_nonneg _
  · apply D.top_eigen_of_equality (kernelOperator_positive hm hn)
    rw [ha,hf]
    simpa only [one_pow,mul_one] using le_antisymm hb hl

end
end «2610.05164v2».GroundState
