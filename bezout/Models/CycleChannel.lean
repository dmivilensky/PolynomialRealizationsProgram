import bezout.Models.CycleSpectrum
import bezout.Models.NetworkExecution
import bezout.Channel.Roots.Coordinates

/-!
Article: bezout, the literal network instance of Proposition D.1.
Use: a genuine real orthonormal cycle basis and the normalized antisymmetric
embedding transport actual finite noisy oracle executions, products and variance
to the full physical two-network model, without a supplied spectral assumption.
Proof: actual cycle diagonalization intertwines every noisy oracle call; causal
execution and squared Euclidean errors commute with the two exact isometries.
-/

namespace bezout.Models.Network
noncomputable section
open scoped BigOperators
open MeasureTheory
variable (m : ℕ) [NeZero m]

/-- The actual active cycle oracle in genuine real orthonormal spectral coordinates. -/
theorem cycleOracle_spectral {N : ℕ} (κ δ : ℝ) (ξ : Fin N → ℝ) (s : Fin N)
    (u : EuclideanSpace ℝ (Fin m)) :
    (realEigenbasis m).repr
      (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s ((realEigenbasis m).repr.symm u))=
      Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ s u := by
  let v := (realEigenbasis m).repr.symm u
  have he : activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s v=
      (4+2*(2/(κ-1)))⁻¹ • cycleOperator m v+
      ((4+2*(2/(κ-1)))⁻¹*(2*(2/(κ-1)))) • v+(δ*ξ s) • v := by
    ext i
    simp only [activeOracle,PiLp.toLp_apply,PiLp.add_apply,PiLp.smul_apply,
      Pi.add_apply,Pi.smul_apply,cycleOperator_apply,smul_eq_mul,cycleLaplacian,
      LinearMap.coe_mk,AddHom.coe_mk]
    ring
  rw [he,map_add,map_add,map_smul,map_smul,map_smul]
  ext j
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,realEigenbasis_diagonalization,
    v,LinearIsometryEquiv.apply_symm_apply]
  change _=(activeSpectralValue m κ j+δ*ξ s)*u j
  unfold activeSpectralValue
  ring

/-- Every actual active-cycle history output equals the transported spectral-coordinate output. -/
theorem cycle_output_spectral {N : ℕ} (h : bezout.History N) (κ δ : ℝ) (ξ : Fin N → ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) :
    h.oracleOutput ((realEigenbasis m).repr.symm initial)
      (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ)=
    (realEigenbasis m).repr.symm
      (h.oracleOutput initial (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ)) := by
  apply h.oracleOutput_map (realEigenbasis m).repr.symm.toLinearEquiv.toLinearMap
  intro s u
  apply (realEigenbasis m).repr.injective
  change (realEigenbasis m).repr
    (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s ((realEigenbasis m).repr.symm u))=
    (realEigenbasis m).repr ((realEigenbasis m).repr.symm
      (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ s u))
  rw [cycleOracle_spectral,LinearIsometryEquiv.apply_symm_apply]

/-- The full physical network output is its genuinely isometric spectral-coordinate output. -/
theorem cycle_network_output_spectral {N : ℕ} (h : bezout.History N) (κ δ : ℝ)
    (ξ : Fin N → ℝ) (initial : EuclideanSpace ℝ (Fin m)) :
    h.oracleOutput (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ ξ)=
      activeEmbedding ((realEigenbasis m).repr.symm (h.oracleOutput initial
        (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ))) := by
  rw [network_output_active,cycle_output_spectral]

omit [NeZero m] in
/-- The literal diagonal channel oracle is the differentiated Hessian-perturbation oracle. -/
theorem spectralOracle_eq_perturbed {N : ℕ} (eig : Fin m → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Channel.Roots.euclideanOracle eig δ ξ=
      bezout.History.perturbedOracle (bezout.History.matrixEnd (Matrix.diagonal eig))
        (fun s => ξ s • (LinearMap.id : Module.End ℝ (EuclideanSpace ℝ (Fin m)))) δ := by
  funext s
  ext u j
  change (eig j+δ*ξ s)*u j=(Matrix.diagonal eig).mulVec u.ofLp j+δ*(ξ s*u j)
  simp only [Matrix.mulVec,Matrix.diagonal,Matrix.of_apply,dotProduct,ite_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  ring

/-- The article's signal matrix differentiates the actual full physical network iteration. -/
theorem cycle_network_hasDerivAt {N : ℕ} (h : bezout.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun t => h.oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) t (fun s => e s)))
      (activeEmbedding ((realEigenbasis m).repr.symm
        (Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))) 0 := by
  let R : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 2×ZMod m) :=
    activeEmbedding.toContinuousLinearMap.comp (realEigenbasis m).repr.symm.toContinuousLinearMap
  have hd := R.hasFDerivAt.comp_hasDerivAt 0
    (Channel.hasDerivAt_signal_output h (activeSpectralValue m κ) initial e)
  convert hd using 1
  · funext t
    rw [cycle_network_output_spectral,spectralOracle_eq_perturbed]
    rfl
  · rfl

/-- Literal finite-noise spectral-coordinate variance is the actual ambient network variance. -/
theorem cycle_network_mse_spectral {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : bezout.History N) (κ δ : ℝ) (ξ : Ω → Fin N → ℝ)
    (initial nominal : EuclideanSpace ℝ (Fin m)) :
    (∫ ω,‖h.oracleOutput (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ (ξ ω))-
      activeEmbedding ((realEigenbasis m).repr.symm nominal)‖^2 ∂μ)=
      ∫ ω,‖h.oracleOutput initial
        (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ (ξ ω))-nominal‖^2 ∂μ := by
  rw [network_mse_active]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only
    rw [cycle_output_spectral,← map_sub,LinearIsometryEquiv.norm_map])

/-- The exact root-step product variance is the full physical two-network terminal variance. -/
theorem cycle_network_root_variance {N : ℕ} (α : Fin N → ℝ) (κ δ : ℝ)
    (a : Fin m → ℝ) :
    (∫ ω,‖(Channel.Roots.history α).oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2 a)))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ
        (fun s => Probability.SignProducts.sign s ω))-
      activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2
        (fun j => (Channel.Roots.terminal α).eval (activeSpectralValue m κ j)*a j)))‖^2
      ∂Probability.Signs.law N)=
    ∑ j,a j^2*((∏ s,((1-α s*activeSpectralValue m κ j)^2+δ^2*α s^2))-
      (Channel.Roots.terminal α).eval (activeSpectralValue m κ j)^2) := by
  rw [cycle_network_mse_spectral]
  exact Channel.Roots.euclidean_mode_variance α (activeSpectralValue m κ) a δ

/-- Every iid channel-sign law has exactly the same full ambient terminal distribution
under any root ordering, for the literal physical two-network oracle. -/
theorem cycle_network_root_distribution_permute {N : ℕ} (α : Fin N → ℝ) (κ δ : ℝ)
    (a : Fin m → ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν] (e : Equiv.Perm (Fin N)) :
    Measure.map (fun ω : Fin N → Bool => (Channel.Roots.history (α ∘ e)).oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2 a)))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ
        (fun s => Probability.SignProducts.sign s ω))) (Measure.pi (fun _ : Fin N => ν))=
    Measure.map (fun ω : Fin N → Bool => (Channel.Roots.history α).oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2 a)))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ
        (fun s => Probability.SignProducts.sign s ω))) (Measure.pi (fun _ : Fin N => ν)) := by
  let f : (Fin N → Bool) → EuclideanSpace ℝ (Fin 2×ZMod m) := fun ω =>
    (Channel.Roots.history α).oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2 a)))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ
        (fun s => Probability.SignProducts.sign s ω))
  have he : (fun ω : Fin N → Bool => (Channel.Roots.history (α ∘ e)).oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm (WithLp.toLp 2 a)))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ
        (fun s => Probability.SignProducts.sign s ω)))=
      fun ω => f (Probability.SignProducts.permute e.symm ω) := by
    funext ω
    dsimp only [f]
    rw [cycle_network_output_spectral,cycle_network_output_spectral,
      Channel.Roots.euclidean_mode_product,Channel.Roots.euclidean_mode_product]
    simp only [Channel.Roots.finiteMultiplier_permute]
    rfl
  rw [he]
  change Measure.map (f ∘ Probability.SignProducts.permute e.symm) _=Measure.map f _
  rw [← Measure.map_map (measurable_of_finite f)
    (Channel.Roots.iid_measurePreserving_permute ν e.symm).measurable,
    (Channel.Roots.iid_measurePreserving_permute ν e.symm).map_eq]

/-- The actual ambient network derivative has exactly the signal-matrix output norm. -/
theorem cycle_network_derivative_norm {N : ℕ} (h : bezout.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    ‖activeEmbedding ((realEigenbasis m).repr.symm
      (Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))‖=
      ‖Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e‖ := by
  rw [LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]

/-- Literal cyclic-network LF/Prefix operator gains have the sharp square-root ratio. -/
theorem cycle_lf_operator_isEquivalent (κ : ℝ) (hκ : 1<κ) (hm : Even m)
    (a : Fin m → ℝ) (w : ℝ) (hw : 0<w)
    (ha0 : a (lowerMode m)^2=w) (ha1 : a (upperMode m)^2=w) :
    let S := cycleFiniteSignal m κ hκ hm a w hw ha0 ha1
    Asymptotics.IsEquivalent Filter.atTop
      (fun k => Channel.rectangularNorm
        (Comparisons.RootAsymptotics.rootMatrix S (Comparisons.RootAsymptotics.dyadicHorizon k)
          (Channel.Roots.dyadicPermutation (k+1)))/
        Channel.rectangularNorm (Comparisons.RootAsymptotics.prefixMatrix S
          (Comparisons.RootAsymptotics.dyadicHorizon k)))
      (fun k => Real.sqrt (Comparisons.RootAsymptotics.dyadicHorizon k)/2) :=
  Comparisons.RootAsymptotics.lf_operator_isEquivalent _

/-- Literal cyclic-network LF/Prefix squared HS gains have the sharp linear ratio. -/
theorem cycle_lf_hs_isEquivalent (κ : ℝ) (hκ : 1<κ) (hm : Even m)
    (a : Fin m → ℝ) (w : ℝ) (hw : 0<w)
    (ha0 : a (lowerMode m)^2=w) (ha1 : a (upperMode m)^2=w) :
    let S := cycleFiniteSignal m κ hκ hm a w hw ha0 ha1
    Asymptotics.IsEquivalent Filter.atTop
      (fun k => Channel.rectangularHsSq
        (Comparisons.RootAsymptotics.rootMatrix S (Comparisons.RootAsymptotics.dyadicHorizon k)
          (Channel.Roots.dyadicPermutation (k+1)))/
        Channel.rectangularHsSq (Comparisons.RootAsymptotics.prefixMatrix S
          (Comparisons.RootAsymptotics.dyadicHorizon k)))
      (fun k => (Comparisons.RootAsymptotics.dyadicHorizon k:ℝ)/2) :=
  Comparisons.RootAsymptotics.lf_hs_isEquivalent _

end
end bezout.Models.Network
