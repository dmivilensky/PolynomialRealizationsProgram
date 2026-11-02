import bezout.Models.Network
import bezout.History.Transport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: bezout, actual finite-noise network execution on the active subspace.
Use: the normalized antisymmetric embedding is genuinely Euclidean isometric;
the full physical two-network oracle reduces to the active-coordinate oracle
at every actual causal query, so terminal variance has no hidden factor two.
Proof: sum the two equal squared coordinate blocks and apply causal intertwining.
-/

namespace bezout.Models.Network
noncomputable section
open scoped BigOperators
variable {J : Type*} [Fintype J]

/-- The normalized physical disagreement embedding into both Euclidean networks. -/
def activeEmbeddingLinear : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ (Fin 2×J) where
  toFun z := WithLp.toLp 2 (fun ij => (if ij.1=0 then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹)*z ij.2)
  map_add' z w := by ext ij; simp only [PiLp.add_apply]; ring
  map_smul' c z := by ext ij; simp only [PiLp.smul_apply, smul_eq_mul,
    RingHom.id_apply]; ring

/-- The normalized embedding preserves the full Euclidean squared distance. -/
theorem activeEmbedding_norm_sq (z : EuclideanSpace ℝ J) :
    ‖activeEmbeddingLinear z‖^2=‖z‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [activeEmbeddingLinear, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type, Fin.sum_univ_two, ite_true,
    show (1:Fin 2)≠0 by decide, ite_false, mul_pow, neg_pow_two]
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  simp only [inv_pow, hs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual Euclidean isometric inclusion of active disagreement coordinates. -/
def activeEmbedding : EuclideanSpace ℝ J →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2×J) where
  toLinearMap := activeEmbeddingLinear
  norm_map' z := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (activeEmbedding_norm_sq z)

/-- The two physical network blocks of a Euclidean state. -/
def networkBlocks (x : EuclideanSpace ℝ (Fin 2×J)) : (J → ℝ)×(J → ℝ) :=
  (fun j => x (0,j), fun j => x (1,j))

/-- Reassemble the two physical vector blocks into the ambient Euclidean state. -/
def ofNetworkBlocks (x : (J → ℝ)×(J → ℝ)) : EuclideanSpace ℝ (Fin 2×J) :=
  WithLp.toLp 2 (fun ij => if ij.1=0 then x.1 ij.2 else x.2 ij.2)

/-- The normalized embedding is precisely the reassembled antisymmetric pair. -/
theorem activeEmbedding_blocks (z : EuclideanSpace ℝ J) :
    activeEmbedding z=ofNetworkBlocks (antisymmetric ((Real.sqrt 2)⁻¹ • z.ofLp)) := by
  ext ⟨i,j⟩
  fin_cases i <;> simp [activeEmbedding, activeEmbeddingLinear, ofNetworkBlocks, antisymmetric]

/-- The literal block Hessian plus the shared fluctuating channel. -/
def ambientOracle {N : ℕ} (Lc : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (a δ : ℝ)
    (ξ : Fin N → ℝ) (s : Fin N) (x : EuclideanSpace ℝ (Fin 2×J)) :
    EuclideanSpace ℝ (Fin 2×J) :=
  ofNetworkBlocks (hessian Lc a (networkBlocks x)+(δ*ξ s) • projector (networkBlocks x))

/-- The corresponding active Euclidean oracle on one disagreement coordinate block. -/
def activeOracle {N : ℕ} (Lc : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (a δ : ℝ)
    (ξ : Fin N → ℝ) (s : Fin N) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 ((4+2*a)⁻¹ • (Lc z.ofLp+(2*a) • z.ofLp)+(δ*ξ s) • z.ofLp)

/-- Actual physical block action intertwines the normalized active inclusion. -/
theorem ambientOracle_embedding {N : ℕ} (Lc : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (a δ : ℝ)
    (ξ : Fin N → ℝ) (s : Fin N) (z : EuclideanSpace ℝ J) :
    ambientOracle Lc a δ ξ s (activeEmbedding z)=activeEmbedding (activeOracle Lc a δ ξ s z) := by
  have hb : networkBlocks (activeEmbedding z)=
      antisymmetric ((Real.sqrt 2)⁻¹ • z.ofLp) := by
    ext j <;> simp [networkBlocks, activeEmbedding, activeEmbeddingLinear, antisymmetric]
  unfold ambientOracle
  rw [hb, hessian_antisymmetric, projector_antisymmetric, activeEmbedding_blocks]
  congr 1
  ext j <;> simp [activeOracle, antisymmetric, map_smul] <;> ring

/-- Every physical query and finite terminal output reduce exactly to active coordinates. -/
theorem network_output_active {N : ℕ} (h : bezout.History N)
    (Lc : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (a δ : ℝ) (ξ : Fin N → ℝ) (initial : EuclideanSpace ℝ J) :
    h.oracleOutput (activeEmbedding initial) (ambientOracle Lc a δ ξ)=
      activeEmbedding (h.oracleOutput initial (activeOracle Lc a δ ξ)) :=
  h.oracleOutput_map activeEmbedding.toLinearMap initial _ _ (ambientOracle_embedding Lc a δ ξ)

/-- Full physical network terminal variance equals its active Euclidean prediction exactly. -/
theorem network_mse_active {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : bezout.History N)
    (Lc : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (a δ : ℝ) (ξ : Ω → Fin N → ℝ)
    (initial nominal : EuclideanSpace ℝ J) :
    (∫ ω, ‖h.oracleOutput (activeEmbedding initial) (ambientOracle Lc a δ (ξ ω))-
      activeEmbedding nominal‖^2 ∂μ)=
    ∫ ω, ‖h.oracleOutput initial (activeOracle Lc a δ (ξ ω))-nominal‖^2 ∂μ :=
  h.oracleOutput_mse_isometry (E := EuclideanSpace ℝ J)
    (F := EuclideanSpace ℝ (Fin 2×J)) μ (activeEmbedding (J := J)) initial nominal
    (fun ω => activeOracle Lc a δ (ξ ω)) (fun ω => ambientOracle Lc a δ (ξ ω))
    (fun ω => ambientOracle_embedding Lc a δ (ξ ω))

end
end bezout.Models.Network
