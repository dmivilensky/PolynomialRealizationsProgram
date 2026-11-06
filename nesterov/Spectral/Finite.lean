import nesterov.Spectral.Realization
import polyak.Waves.Finite
import polyak.Functions.Embedding

/-! Finite spectra are realized in J complex coordinates, of real dimension 2J.
The sampling map and all its inner-product identities are reused from Polyak. -/
noncomputable section
open scoped BigOperators NNReal
namespace nesterov.Spectral
open polyak.Interpolation
variable {J : Type*} [Fintype J]

abbrev finiteSpectrum := @polyak.Waves.finiteSpectrum
abbrev finiteLift := @polyak.Waves.finiteLift

def finitePosition (w : J → ℝ≥0) (c : J → Frequency) (a : SymbolPair)
    (t : ℝ) (i : Option ℕ) : EuclideanSpace ℂ J := finiteLift w c (positionMap a t i)

def finiteGradient (w : J → ℝ≥0) (c : J → Frequency) (a : SymbolPair)
    (t : ℝ) (i : Option ℕ) : EuclideanSpace ℂ J := finiteLift w c (gradientMap a t i)

def finiteLatent (w : J → ℝ≥0) (c : J → Frequency) (t : ℝ) (k : ℕ) :
    EuclideanSpace ℂ J := finiteLift w c (polyak.Waves.positionMap t (some k))

theorem finite_tableFeasible_iff (w : J → ℝ≥0) (c : J → Frequency)
    (hw : ∑ j, w j = 1) (a : SymbolPair) (C t : ℝ) :
    TableFeasible (finitePosition w c a t) (finiteGradient w c a t)
      (mixtureValue (finiteSpectrum w c hw) a C t) ↔ Feasible a t (finiteSpectrum w c hw) C := by
  rw [← mixture_tableFeasible_iff]
  have hR (i j : Option ℕ) :
      datumR (finitePosition w c a t) (finiteGradient w c a t) i j =
        datumR (mixturePosition (finiteSpectrum w c hw) a t)
          (mixtureGradient (finiteSpectrum w c hw) a t) i j :=
    polyak.Waves.datumR_finiteLift w c hw (positionMap a t) (gradientMap a t) i j
  have hT (i j : Option ℕ) :
      datumT (finitePosition w c a t) (finiteGradient w c a t)
          (mixtureValue (finiteSpectrum w c hw) a C t) i j =
        datumT (mixturePosition (finiteSpectrum w c hw) a t)
          (mixtureGradient (finiteSpectrum w c hw) a t)
          (mixtureValue (finiteSpectrum w c hw) a C t) i j :=
    polyak.Waves.datumT_finiteLift w c hw (positionMap a t) (gradientMap a t) _ i j
  constructor
  · intro h i j
    rw [← hR i j, ← hT i j]
    exact h i j
  · intro h i j
    rw [hR i j, hT i j]
    exact h i j

omit [Fintype J] in
@[simp] theorem finitePosition_none (w : J → ℝ≥0) (c : J → Frequency) (a : SymbolPair) (t : ℝ) :
    finitePosition w c a t none = 0 := by
  have he : positionMap a t none = 0 := by
    ext s; simp [positionMap, polyak.Waves.positionMap, polyak.Waves.position]
  simp [finitePosition, he]

omit [Fintype J] in
@[simp] theorem finiteGradient_none (w : J → ℝ≥0) (c : J → Frequency) (a : SymbolPair) (t : ℝ) :
    finiteGradient w c a t none = 0 := by
  have he : gradientMap a t none = 0 := by
    ext s; simp [gradientMap, polyak.Waves.positionMap, polyak.Waves.position]
  simp [finiteGradient, he]

theorem finite_interpolation_iff (w : J → ℝ≥0) (c : J → Frequency)
    (hw : ∑ j, w j = 1) (a : SymbolPair) (C t : ℝ) :
    (∃ ψ : EuclideanSpace ℂ J → ℝ, polyak.NormalizedSmooth ψ ∧ ∀ i,
      ψ (finitePosition w c a t i) = mixtureValue (finiteSpectrum w c hw) a C t i ∧
      gradient ψ (finitePosition w c a t i) = finiteGradient w c a t i) ↔
      Feasible a t (finiteSpectrum w c hw) C := by
  exact (interpolation_iff none (finitePosition_none w c a t) (finiteGradient_none w c a t)
    (mixtureValue_none _ a C t)).trans (finite_tableFeasible_iff w c hw a C t)

theorem norm_finiteLatent (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (t : ℝ) (k : ℕ) : ‖finiteLatent w c t k‖ = Real.exp (k*t) := by
  have hs := polyak.Waves.norm_sq_finiteLift_eq_lift w c hw (polyak.Waves.positionMap t (some k))
  change ‖finiteLatent w c t k‖ ^ 2 = ‖latent (finiteSpectrum w c hw) t k‖ ^ 2 at hs
  rw [norm_latent] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hs

omit [Fintype J] in
theorem finiteLatent_sum (w : J → ℝ≥0) (c : J → Frequency) (t : ℝ)
    (d : ℕ) (a : Fin d → ℝ) (k : ℕ) (q : C(Frequency, ℂ))
    (hq : ∀ s, q s = ∑ j, (a j : ℂ) * polyak.Waves.z t (Real.arccos s) ^ j.val) :
    (∑ j, a j • finiteLatent w c t (k+j)) =
      finiteLift w c (q * polyak.Waves.positionMap t (some k)) := by
  simp only [finiteLatent, ← map_smul, ← map_sum]
  congr 1
  ext s
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    polyak.Waves.positionMap, polyak.Waves.position, ContinuousMap.mul_apply, hq,
    Complex.real_smul, pow_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [ContinuousMap.coe_mk]
  ring

theorem query_finiteLatent (M : StationaryMethod) (μ L : ℝ) (w : J → ℝ≥0)
    (c : J → Frequency) (t : ℝ) (k : ℕ) :
    M.query (finiteLatent w c t) k = finitePosition w c (M.symbolPair μ L t) t (some k) := by
  unfold StationaryMethod.query finitePosition positionMap
  apply finiteLatent_sum w c t M.memory M.queryCoeff k
  intro s
  exact M.queryPolynomial_complex_eval _

omit [Fintype J] in
theorem normalized_finiteLatent (M : StationaryMethod) (μ L : ℝ) (w : J → ℝ≥0)
    (c : J → Frequency) (t : ℝ) (k : ℕ) :
    (∑ j : Fin (M.memory+1), M.normalizedCoeff μ L j • finiteLatent w c t (k+j)) =
      finiteGradient w c (M.symbolPair μ L t) t (some k) := by
  unfold finiteGradient gradientMap
  apply finiteLatent_sum w c t (M.memory+1) (M.normalizedCoeff μ L) k
  intro s
  change ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval _ = _
  rw [M.normalizedPolynomial_eq_sum]
  simp only [Polynomial.eval_map, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  rfl

/-- Exact finite-dimensional realization, allowing zero weights and repeated atoms. -/
theorem finite_exists_objective (M : StationaryMethod) {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (w : J → ℝ≥0) (c : J → Frequency)
    (hw : ∑ j, w j = 1) (h : Feasible (M.symbolPair μ L t) t (finiteSpectrum w c hw) C) :
    ∃ f : EuclideanSpace ℂ J → ℝ, polyak.CenteredSmoothStronglyConvex μ L f ∧
      M.IsTrajectory (gradient f) (finiteLatent w c t) := by
  obtain ⟨ψ, hψ, hdata⟩ := (finite_interpolation_iff w c hw (M.symbolPair μ L t) C t).mpr h
  refine ⟨polyak.denormalizeFunction μ L ψ, hψ.denormalize hμ hμL,
    M.isTrajectory_denormalize hμL hψ.differentiable ?_⟩
  intro k
  rw [normalized_finiteLatent, query_finiteLatent M μ L]
  exact (hdata (some k)).2.symm

theorem finite_real_dimension : Module.finrank ℝ (EuclideanSpace ℂ J) = 2 * Fintype.card J := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

/-- A literal isometric coordinate identification with R^(2J). -/
def finiteRealCoordinates : EuclideanSpace ℂ J →ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (2*Fintype.card J)) := by
  rw [← finite_real_dimension (J := J)]
  exact (stdOrthonormalBasis ℝ (EuclideanSpace ℂ J)).repr.toLinearIsometry

/-- The same finite spectrum gives one genuine objective and one exact
trajectory in the article's literal real dimension 2J. -/
theorem finite_exists_real_objective (M : StationaryMethod) {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (w : J → ℝ≥0) (c : J → Frequency)
    (hw : ∑ j,w j=1) (h : Feasible (M.symbolPair μ L t) t (finiteSpectrum w c hw) C) :
    ∃ (f : EuclideanSpace ℝ (Fin (2*Fintype.card J)) → ℝ)
      (x : ℕ → EuclideanSpace ℝ (Fin (2*Fintype.card J))),
      polyak.CenteredSmoothStronglyConvex μ L f ∧ M.IsTrajectory (gradient f) x ∧
        ∀ k, ‖x k‖=Real.exp (k*t) := by
  obtain ⟨f,hf,ht⟩ := finite_exists_objective M hμ hμL w c hw h
  let e := finiteRealCoordinates (J := J)
  refine ⟨polyak.extendObjective μ L e f,fun k => e (finiteLatent w c t k),
    hf.extendObjective e,?_,fun k => ?_⟩
  · intro k
    have hq : M.query (fun j => e (finiteLatent w c t j)) k=e (M.query (finiteLatent w c t) k) := by
      simp [StationaryMethod.query,map_sum,map_smul]
    rw [hq,polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex e]
    simpa only [map_sum,map_smul] using congrArg e (ht k)
  · rw [e.norm_map]
    exact norm_finiteLatent w c hw t k

end nesterov.Spectral
