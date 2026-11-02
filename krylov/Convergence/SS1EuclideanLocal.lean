import krylov.Convergence.SS1MetricLocal
import krylov.Convergence.SlidingMetricProbe
import krylov.LinearAlgebra.SpectralEndpoints
import krylov.LinearAlgebra.SpectralUpperForm

/-!
Article: main_krylov, lem:ss1-local, exact Euclidean determinant hypothesis.
Use: derive the normalized Hstar-frame inverse bound from the article's
actual Euclidean unit-column determinant separation, then prove a common
physical starting ball and the actual termination-or-convergence result.
Source: finite determinant compactness, positive-root gain transport,
and the true sequential secant invariant-ball estimate.
-/

/-!
Article: krylov, Lemma E.20 [lem:ss1-local].

Starting sufficiently near the nondegenerate minimum, the genuine physical SS1 sequence with
the original Euclidean determinant bound either terminates or converges with the asserted
R-order.
The hypothesis is on every nonstationary window; the theorem explicitly includes stationary
termination and derives metric-window inverse bounds from the original determinant.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1500000

/-- Original Euclidean determinant separation supplies a uniform inverse
bound on the actual Hstar-normalized frame, without assuming it. -/
theorem physical_determinant_metric_inverse
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    {mu upper σ₀ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ₀ : 0<σ₀)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2) :
    ∃ C : ℝ,0<C ∧∀ s : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)),
      σ₀≤|(windowMatrix (unitWindow s)).det| →
      IsUnit (windowMatrix (unitWindow (fun i=>metricCoordinates base hb (s i)))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>metricCoordinates base hb (s i))))⁻¹‖≤C := by
  obtain ⟨Cflat,hCf,hbound⟩:=unit_window_determinant_inverse (n:=n+1) hσ₀
  let σH:=Cflat⁻¹*Real.sqrt (mu/upper)
  have hσH : 0<σH:=mul_pos (inv_pos.mpr hCf) (Real.sqrt_pos.mpr (div_pos hmu hu))
  refine ⟨σH⁻¹,inv_pos.mpr hσH,fun s hdet=>?_⟩
  have hV : IsUnit (windowMatrix (unitWindow s)).det:=isUnit_iff_ne_zero.mpr (abs_pos.mp (hσ₀.trans_le hdet))
  have hs (i : Fin (n+1)) : s i≠0 := by
    intro hz
    apply windowMatrix_step_ne_zero (unitWindow s) hV i
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  have hinv:=(hbound (unitWindow s) (unitWindow_norm s hs) hdet).2
  have hlow : Cflat⁻¹≤leastGain (windowMatrix (unitWindow s)):=inv_anti₀ (inverse_norm_pos _ hV) hinv
  have hgain (c : Fin (n+1) → ℝ) :
      (Cflat⁻¹)^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2 := by
    have ha:=leastGain_action (windowMatrix (unitWindow s)) hV (WithLp.toLp 2 c)
    have hh:=(mul_le_mul_of_nonneg_right hlow (norm_nonneg (WithLp.toLp 2 c))).trans ha
    have hh' : Cflat⁻¹*‖WithLp.toLp 2 c‖≤‖combine (unitWindow s) c‖ := by
      simpa only [combine_windowMatrix] using hh
    exact (by simpa only [mul_pow] using
      (sq_le_sq₀ (by positivity : 0≤Cflat⁻¹*‖WithLp.toLp 2 c‖) (norm_nonneg _)).mpr hh')
  have hmetric:=metric_full_window_leastGain base hb s hmu hu (inv_pos.mpr hCf) hlower hupper hgain
  exact ⟨hmetric.1,krylov.Secant.inverse_bound_of_leastGain _ hmetric.1 hσH hmetric.2⟩

/-- The original local SS1 lemma with Euclidean starting points and
Euclidean unit-step determinants. The determinant condition is required
only while the actual current iterate has not reached the minimizer. -/
theorem ss1_local_original_physical_convergence
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (center : EuclideanSpace ℝ (Fin (n+1))) (S : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hS : Convex ℝ S) (hn : S∈𝓝 center)
    {LE : ℝ≥0} (hH : LipschitzOnWith LE H S) (hbase : H center=cgOperator base)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G center=0)
    {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    ∃ r₀ : ℝ,0<r₀ ∧∀ seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
      (∀ i,‖seed i-center‖≤r₀) →
      (∀ k,ss1Sequence G seed (k+n+1)≠center →
        σ₀≤|(windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence G seed) k))).det|) →
      (∃ k,n+1≤k ∧ss1Sequence G seed k=center) ∨
      Tendsto (ss1Sequence G seed) atTop (𝓝 center) ∧
      ((fun k=>metricCoordinates base hb (ss1Sequence G seed (k+1)-center))=o[atTop]
        (fun k=>‖metricCoordinates base hb (ss1Sequence G seed k-center)‖)) ∧
      HasROrder (fun k=>‖metricCoordinates base hb (ss1Sequence G seed k-center)‖) (oneGradientRoot (n+2)) := by
  let T:=metricCoordinates base hb
  let mu:=spectralLower base hb.1
  let upper:=spectralUpper base hb.1
  have hmu : 0<mu:=spectralLower_pos base hb
  have hu : 0<upper:=spectralUpper_pos base hb
  have hlower (v : EuclideanSpace ℝ (Fin (n+1))) : mu*‖v‖^2≤ inner ℝ v (cgOperator base v):=
    spectral_lower_form base hb.1 (spectralLower_le base hb.1) v
  have hupper (v : EuclideanSpace ℝ (Fin (n+1))) : inner ℝ v (cgOperator base v)≤upper*‖v‖^2:=
    spectral_upper_form base hb.1 (le_spectralUpper base hb.1) v
  obtain ⟨C,hC,hframe⟩:=physical_determinant_metric_inverse base hb hmu hu hσ₀ hlower hupper
  let Gh:=centeredMetricGradient T center G
  let Hh:=centeredMetricHessian T center H
  let Sh:=centeredMetricDomain T center S
  let L:ℝ≥0:=Real.toNNReal ((LE:ℝ)*mu^(-(3/2:ℝ)))
  have hSh : Convex ℝ Sh:=centeredMetricDomain_convex T center hS
  have hnh : Sh∈𝓝 (0:EuclideanSpace ℝ (Fin (n+1))):=centeredMetricDomain_mem_nhds T center hn
  obtain ⟨R,hR,hRad⟩:=local_source_closedBall_radius Sh hnh L
  let B:=1+((n+1:ℕ):ℝ)*C^2
  let r:=min R (8*((L:ℝ)+1)*B)⁻¹
  have hB : 0<B:=by dsimp only [B];positivity
  have hr : 0<r:=lt_min hR (inv_pos.mpr (by positivity))
  have hrR : r≤R:=min_le_left _ _
  have hrad : r*(8*((L:ℝ)+1)*B)≤1:=by
    exact (le_div_iff₀ (by positivity : 0<8*((L:ℝ)+1)*B)).mp
      (by simpa only [one_div] using min_le_right R (8*((L:ℝ)+1)*B)⁻¹)
  have hsmall : 2*(L:ℝ)*r*(1+(n+1)*C^2)≤1/2 := by
    have hp : 0≤r*B:=mul_nonneg hr.le hB.le
    have hh : 2*(L:ℝ)*r*B≤1/2:=by nlinarith only [hrad,hp]
    simpa only [B,Nat.cast_add,Nat.cast_one] using hh
  let r₀:=r/(Real.sqrt upper+1)
  refine ⟨r₀,div_pos hr (by positivity),fun seed hseed hdet=>?_⟩
  by_cases hterm : ∃ k,n+1≤k ∧ss1Sequence G seed k=center
  · exact Or.inl hterm
  apply Or.inr
  let sh:=fun i=>T (seed i-center)
  have he (k : ℕ) : T (ss1Sequence G seed k-center)=ss1Sequence Gh sh k:=by
    rw [ss1Sequence_translate]
    exact ss1Sequence_coordinate T (metricCoordinates_inverse_symmetric base hb) _ _ k
  have hfun : (fun k=>T (ss1Sequence G seed k-center))=ss1Sequence Gh sh:=funext he
  have hHh : LipschitzOnWith L Hh Sh:=centeredMetricHessian_lipschitz base hb center H hH hmu hlower
  have hH₀ : Hh 0=ContinuousLinearMap.id ℝ _:=
    coordinateDerivative_metric_zero base hb (fun z=>H (center+z)) (by simpa only [add_zero] using hbase)
  have hGh z (hz : z∈Sh) : HasFDerivAt Gh (Hh z) z:=centeredMetricGradient_hasFDerivAt T center G H z (hG _ hz)
  have hGh₀ : Gh 0=0:=by simp only [Gh,centeredMetricGradient,coordinateGradient,map_zero,add_zero,hG₀]
  have hi (k : ℕ) : IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence Gh sh) k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence Gh sh) k)))⁻¹‖≤C:=by
    have hd:=hdet k (fun hz=>hterm ⟨k+n+1,by omega,hz⟩)
    have hh:=hframe (windowStep (ss1Sequence G seed) k) hd
    have hs:=centered_metric_windowStep (n:=n+1) T center (ss1Sequence G seed) k
    rw [hfun] at hs
    rw [←hs] at hh
    exact hh
  have hseedH (i : Fin (n+2)) : ‖sh i‖≤r := by
    have hbnd:=(metricCoordinates_norm_upper base hb hu hupper (seed i-center)).trans
      (mul_le_mul_of_nonneg_left (hseed i) (Real.sqrt_nonneg _))
    apply hbnd.trans
    have hnonneg:=Real.sqrt_nonneg upper
    dsimp only [r₀]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<Real.sqrt upper+1)).mpr
    nlinarith only [hr,hnonneg]
  have hc:=ss1Sequence_local_convergence Gh Hh Sh hSh hHh hH₀ hGh hGh₀ sh hr hC.le
    ((Metric.closedBall_subset_closedBall hrR).trans (hRad R hR le_rfl).1) hseedH hi hsmall
  have hzero : (0:EuclideanSpace ℝ (Fin (n+1)))∈Sh:=mem_of_mem_nhds hnh
  have hgain : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence Gh sh) k))).det ∧
      C⁻¹≤leastGain (windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence Gh sh) k))) :=
    Filter.Eventually.of_forall fun k=>⟨(hi k).1,inv_anti₀ (inverse_norm_pos _ (hi k).1) (hi k).2⟩
  refine ⟨?_,?_,?_⟩
  · have hp (k : ℕ) : center+T.symm (ss1Sequence Gh sh k)=ss1Sequence G seed k:=by rw [←he,T.symm_apply_apply];abel_nf
    have ht:=(tendsto_const_nhds : Tendsto (fun _ : ℕ=>center) atTop (𝓝 center)).add
      ((T.symm.continuous.tendsto 0).comp hc.2.2)
    simpa only [Function.comp_def,map_zero,add_zero,hp] using ht
  · have hs:=ss1Sequence_superlinear Gh Hh Sh hSh hzero hnh hHh hH₀ hGh hGh₀ sh hc.2.2 (inv_pos.mpr hC) hgain
    change (fun k=>T (ss1Sequence G seed (k+1)-center))=o[atTop](fun k=>‖T (ss1Sequence G seed k-center)‖)
    simpa only [he] using hs
  · have hs:=ss1Sequence_rorder Gh Hh Sh hSh hzero hnh hHh hH₀ hGh hGh₀ sh hc.2.2 (inv_pos.mpr hC) hgain
    change HasROrder (fun k=>‖T (ss1Sequence G seed k-center)‖) _
    simpa only [he] using hs

end
end krylov.Convergence
