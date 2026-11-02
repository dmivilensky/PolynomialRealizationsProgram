import krylov.Functions.GradientIndistinguishable
import krylov.Secant.Model

/-!
Article: main_krylov, thm:struct, the quadratic-plus-hidden-cubic data family.
Use: assemble the actual scalar objective, its derivatives, exact observed
secants, defect and latest-information model. A symmetric continuous bilinear
form is the coordinate-free representation of the article's symmetric matrix A.
Source: Appendix G's explicit polynomial family and the existing secant-model API.
-/

/-!
Article: krylov, Proposition E.10 [thm:struct].

Genuine smooth hidden cubics preserve the full sampled vector-gradient transcript, latest model
and zero observed defect while changing the final compression by the stated rank-one term; the
oldest value defect equals −c/12.
The scalar bilinear differential is transported to the actual Riesz gradient in
quadraticHidden_gradient_transcript/vector_secant.
-/

namespace krylov.Functions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine quadratic scalar potential with symmetric bilinear Hessian.
Article: main_krylov, thm:struct. -/
def quadraticPotential (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ) (x : E) : ℝ :=
  A x x / 2 - b x

/-- The exact differential of the symmetric quadratic potential.
Article: main_krylov, thm:struct.
Proof: differentiate both slots of the actual bilinear form and use symmetry. -/
theorem quadraticPotential_hasFDerivAt (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (x : E) :
    HasFDerivAt (quadraticPotential A b) (A x - b) x := by
  have h := ((A.hasFDerivAt.clm_apply (hasFDerivAt_id x)).mul_const (1 / 2 : ℝ)).sub b.hasFDerivAt
  convert! h using 1
  · ext y
    simp only [quadraticPotential, div_eq_mul_inv, id_eq, one_mul, Pi.sub_apply]
  · ext v
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id_eq, smul_eq_mul]
    rw [hA v x]
    ring

/-- The exact scalar family in the article, in arbitrary linear coordinates.
Article: main_krylov, thm:struct. -/
def quadraticHidden (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (c : ℝ) (x₀ x : E) : ℝ := quadraticPotential A b x + hiddenCubic φ c x₀ x

/-- The whole quadratic-plus-cubic family is genuinely smooth, without a regularity premise.
Article: main_krylov, thm:struct. Proof: continuous bilinear algebra and the proved cubic smoothness. -/
theorem quadraticHidden_contDiff (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (c : ℝ) (x₀ : E) (n : ℕ) : ContDiff ℝ n (quadraticHidden A b φ c x₀) := by
  unfold quadraticHidden
  apply ContDiff.add
  · unfold quadraticPotential
    fun_prop
  · exact hiddenCubic_contDiff φ c x₀ n

/-- Its actual first derivative, with no unproved derivative field.
Article: main_krylov, thm:struct. Proof: add the proved quadratic and cubic differentials. -/
theorem quadraticHidden_hasFDerivAt (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (quadraticHidden A b φ c x₀) (A x - b + hiddenDerivative φ c x₀ x) x := by
  exact (quadraticPotential_hasFDerivAt A b hA x).add (hiddenCubic_hasFDerivAt φ c x₀ x)

/-- The actual second derivative field is precisely A plus the affine hidden Hessian.
Article: main_krylov, thm:struct.
Proof: differentiate the real first derivative, then reuse the proved hidden-Hessian derivative. -/
theorem quadraticHidden_derivative_hasFDerivAt (A : E →L[ℝ] E →L[ℝ] ℝ)
    (b φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (fun y => A y - b + hiddenDerivative φ c x₀ y)
      (A + hiddenHessian φ c x₀ x) x := by
  exact (A.hasFDerivAt.sub_const b).add (hiddenDerivative_hasFDerivAt φ c x₀ x)

/-- The true third differential of the family is the constant rank-one cubic tensor.
Article: main_krylov, thm:struct.
Proof: the constant quadratic Hessian differentiates to zero. -/
theorem quadraticHidden_hessian_hasFDerivAt (A : E →L[ℝ] E →L[ℝ] ℝ)
    (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (fun y => A + hiddenHessian φ c x₀ y)
      ((c • φ).smulRight (coordinateSquare φ)) x := by
  exact (hiddenHessian_hasFDerivAt φ c x₀ x).const_add (𝕜 := ℝ) A

/-- The actual first derivative at every sample is the unchanged quadratic derivative.
Article: main_krylov, thm:struct.
Proof: the genuine sampled coordinates are zero or one, where the hidden derivative vanishes. -/
theorem quadraticHidden_sample_fderiv (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (p : ℕ) (x s : ℕ → E)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) {k : ℕ} (hk : k ≤ p) :
    fderiv ℝ (quadraticHidden A b φ c (x 0)) (x k) = A (x k) - b := by
  have hcoord : φ (x k - x 0) = 0 ∨ φ (x k - x 0) = 1 := by
    rw [hidden_coordinate_of_steps p x s φ hstep hφ hk]
    split_ifs <;> simp
  exact (add_hiddenCubic_hasFDerivAt (quadraticPotential A b) _ φ c (x 0) (x k)
    (quadraticPotential_hasFDerivAt A b hA (x k)) hcoord).fderiv

/-- Every actual sampled differential secant is exactly the original quadratic action.
Article: main_krylov, thm:struct, Y=AS in differential coordinates.
Proof: subtract the two actual endpoint derivatives and use the genuine step recurrence. -/
theorem quadraticHidden_secant_data (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (p : ℕ) (x s : ℕ → E)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) {j : ℕ} (hj : j < p) :
    fderiv ℝ (quadraticHidden A b φ c (x 0)) (x (j + 1)) -
      fderiv ℝ (quadraticHidden A b φ c (x 0)) (x j) = A (s j) := by
  rw [quadraticHidden_sample_fderiv A b φ hA c p x s hstep hφ (by omega),
    quadraticHidden_sample_fderiv A b φ hA c p x s hstep hφ (by omega),
    hstep j hj, map_add]
  abel

/-- The observed scalar pair matrix is exactly the original symmetric quadratic Gram matrix.
Article: main_krylov, thm:struct, observed data.
Proof: pair each genuine differential secant with its actual stored step. -/
theorem quadraticHidden_observation (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (p : ℕ) (x s : ℕ → E)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) :
    (fun i j : Fin p =>
      (fderiv ℝ (quadraticHidden A b φ c (x 0)) (x (j.val + 1)) -
        fderiv ℝ (quadraticHidden A b φ c (x 0)) (x j.val)) (s i.val)) =
      compressBilinear (fun i : Fin p => s i.val) A := by
  funext i j
  rw [quadraticHidden_secant_data A b φ hA c p x s hstep hφ j.isLt]
  exact hA _ _

/-- Every quadratic Gram observation has zero defect and is fixed by the genuine latest model.
Article: main_krylov, thm:struct, D=0 and Tbar=G.
Proof: actual symmetry invokes the existing secant-model identity. -/
theorem quadraticHidden_model {p : ℕ} (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (s : Fin p → E) :
    Secant.defect (compressBilinear s A) = 0 ∧
      Secant.latest (compressBilinear s A) = compressBilinear s A := by
  have hs : (compressBilinear s A).IsSymm := by
    ext i j
    exact hA _ _
  refine ⟨?_, Secant.latest_eq_of_isSymm hs⟩
  rw [Secant.defect, hs.eq, sub_self]

/-- Every symmetric quadratic has exactly zero actual trapezoid defect.
Article: main_krylov, thm:struct.
Proof: expand the bilinear potential and both genuine endpoint differentials. -/
theorem quadraticPotential_trapezoid (A : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (a s : E) :
    quadraticPotential A b (a + s) - quadraticPotential A b a -
      ((A a - b) s + (A (a + s) - b) s) / 2 = 0 := by
  simp only [quadraticPotential, map_add, add_apply, sub_apply]
  rw [hA s a]
  ring

/-- The original oldest value defect recovers the hidden coefficient exactly.
Article: main_krylov, thm:struct, delta_tr=-c/12.
Proof: both endpoint derivatives are the actual quadratic ones; subtract the
proved zero quadratic defect and use the genuine cubic endpoint value gap. -/
theorem quadraticHidden_oldest_defect (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (x₀ s : E) (hs : φ s = 1) :
    quadraticHidden A b φ c x₀ (x₀ + s) - quadraticHidden A b φ c x₀ x₀ -
      ((fderiv ℝ (quadraticHidden A b φ c x₀) x₀) s +
        (fderiv ℝ (quadraticHidden A b φ c x₀) (x₀ + s)) s) / 2 = -c / 12 := by
  have h₀ : fderiv ℝ (quadraticHidden A b φ c x₀) x₀ = A x₀ - b :=
    (add_hiddenCubic_hasFDerivAt (quadraticPotential A b) _ φ c x₀ x₀
      (quadraticPotential_hasFDerivAt A b hA x₀) (Or.inl (by simp))).fderiv
  have h₁ : fderiv ℝ (quadraticHidden A b φ c x₀) (x₀ + s) = A (x₀ + s) - b :=
    (add_hiddenCubic_hasFDerivAt (quadraticPotential A b) _ φ c x₀ (x₀ + s)
      (quadraticPotential_hasFDerivAt A b hA (x₀ + s)) (Or.inr (by simpa using hs))).fderiv
  rw [h₀, h₁]
  unfold quadraticHidden
  linarith only [quadraticPotential_trapezoid A b hA x₀ s, hiddenCubic_endpoint_gap φ c x₀ s hs]

/-- The actual averaged second differential includes exactly the original constant quadratic part.
Article: main_krylov, thm:struct.
Proof: split the genuine integrable Hessian sum and evaluate its constant integral. -/
theorem quadraticHidden_average_hessian (A : E →L[ℝ] E →L[ℝ] ℝ)
    (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ a u : E) :
    chebyshev1.Nonlinear.averagedDerivative (fun x => A + hiddenHessian φ c x₀ x) a u =
      A + chebyshev1.Nonlinear.averagedDerivative (hiddenHessian φ c x₀) a u := by
  let H₀ := A + (-c * (φ x₀ + 1 / 2)) • coordinateSquare φ
  let T := (c • φ).smulRight (coordinateSquare φ)
  have he (x : E) : A + hiddenHessian φ c x₀ x = H₀ + T x := by
    ext v w
    simp only [hiddenHessian, H₀, T, coordinateSquare, smul_apply, map_sub,
      ContinuousLinearMap.smulRight_apply, add_apply, smul_eq_mul]
    ring
  rw [show (fun x => A + hiddenHessian φ c x₀ x) = (fun x => H₀ + T x) from funext he,
    averagedHessian_affine, averaged_hiddenHessian]
  exact (he _).symm

/-- The actual final secant minus the unchanged window model has the printed hidden diagonal.
Article: main_krylov, thm:struct, S^T B_c S-Tbar=(c/2)(1+w_0)u_0u_0^T.
Proof: subtract the actual constant quadratic part after integrating the true Hessian,
then apply the already proved arbitrary window-correction compression. -/
theorem quadraticHidden_final_compression {p : ℕ} (A : E →L[ℝ] E →L[ℝ] ℝ)
    (s : Fin p → E) (i₀ : Fin p) (φ : E →L[ℝ] ℝ)
    (hφ : ∀ i, φ (s i) = if i = i₀ then 1 else 0)
    (c : ℝ) (x₀ a : E) (ha : φ (a - x₀) = 1) (w : Fin p → ℝ) :
    compressBilinear s
      (chebyshev1.Nonlinear.averagedDerivative (fun x => A + hiddenHessian φ c x₀ x) a
        (∑ i, w i • s i)) - compressBilinear s A =
      (c / 2 * (1 + w i₀)) • Matrix.single i₀ i₀ 1 := by
  rw [quadraticHidden_average_hessian]
  have h := hidden_correction_compression s i₀ φ hφ c x₀ a ha w
  ext i j
  have he := congrFun (congrFun h i) j
  simpa only [compressBilinear, add_apply, Matrix.sub_apply, add_sub_cancel_left] using he

end

section Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- All actual sampled gradients of the article's complete scalar family agree with the quadratic.
Article: main_krylov, thm:struct.
Proof: instantiate the genuine Riesz-gradient transcript theorem with the proved quadratic differential. -/
theorem quadraticHidden_gradient_transcript (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (p : ℕ) (x s : ℕ → E)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) :
    ∀ k ≤ p, gradient (quadraticHidden A b φ c (x 0)) (x k) = gradient (quadraticPotential A b) (x k) :=
  hiddenCubic_gradient_transcript p x s φ hstep hφ (quadraticPotential A b)
    (fun k _ => (quadraticPotential_hasFDerivAt A b hA (x k)).differentiableAt) c

/-- The genuine vector gradient secants are the original quadratic actions in Riesz coordinates.
Article: main_krylov, thm:struct, actual vector data Y=AS.
Proof: linear Riesz transport of the already proved exact differential secants. -/
theorem quadraticHidden_vector_secant (A : E →L[ℝ] E →L[ℝ] ℝ) (b φ : E →L[ℝ] ℝ)
    (hA : ∀ x y, A x y = A y x) (c : ℝ) (p : ℕ) (x s : ℕ → E)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) {j : ℕ} (hj : j < p) :
    gradient (quadraticHidden A b φ c (x 0)) (x (j + 1)) -
      gradient (quadraticHidden A b φ c (x 0)) (x j) =
      (InnerProductSpace.toDual ℝ E).symm (A (s j)) := by
  unfold gradient
  rw [← map_sub, quadraticHidden_secant_data A b φ hA c p x s hstep hφ hj]

end Gradient
end krylov.Functions
