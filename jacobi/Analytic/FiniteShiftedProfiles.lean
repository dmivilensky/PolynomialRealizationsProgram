import jacobi.Analytic.FiniteShiftedL1
import jacobi.Analytic.ShiftedJointContinuity
import jacobi.Comparison.GreenSpectral
import jacobi.Analysis.WeightedSeriesNormed

/-!
Article: jacobi, Theorem C.5.
The actual finite shifted diagonal spectral sum converges along every
cofinal physical row and every convergent compact shift sequence to
the original shifted profile. All actual eigenvector and denominator
bounds are discharged by the preceding unconditional theorems.
Use: finiteShiftedDiagonal_matrix identifies this sum with the original complex matrix resolvent, and the full uniform profile limit proves D.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology

/-- The genuine shifted finite diagonal spectral sum in the source
physical normalization, with the actual finite signed eigenvectors.
Use: finiteShiftedDiagonal_matrix identifies this sum with the original
complex matrix resolvent, and the full uniform profile limit proves D.
Article: jacobi, Theorem C.5.
-/
def finiteShiftedDiagonal (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) (w:ℂ) : ℂ :=
  ∑'k,finiteShiftedEdge a b ha hb n k w*(scaledTargetEigenvector a b ha hb n i k:ℂ)^2

/-- The actual finite shifted diagonal spectral sums have the original
shifted continuum-profile limit along every cofinal moving physical
row and convergent sequence of shifts in an actual compact slit set.
Use: compactness upgrades this true sequential result to the full
uniform compact-parameter conclusions of Theorem C.5.
Article: jacobi, Theorem C.5.
Proof: write each actual shifted coefficient as its original real
spectral weight times its genuine inverse denominator. These bounded
inverse factors multiply the uniformly bounded true eigenvector squares.
The actual real weights converge in L1; each genuine spectral observable
converges by the signed vector limit and continuity away from the proved
limiting poles. Banach-valued spectral summation gives the source series. -/
theorem finiteShiftedDiagonal_moving_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    {t:Interval} (hit:Tendsto (fun r => matrixMesh (ns r) (i r)) atTop (𝓝 (t:ℝ)))
    (w:ℕ→W) {w0:W} (hw:Tendsto w atTop (𝓝 w0)) :
    Tendsto (fun r => finiteShiftedDiagonal a b ha hb (ns r) (i r) (w r)) atTop
      (𝓝 (shiftedProfile a ha t w0)) := by
  -- The original real L1 spectrum is retained as the summation weight throughout.
  obtain ⟨C,hC,hden⟩ := finite_denominator_compact ha hb hW hsub
  obtain ⟨B,hB,hvec⟩ := scaledTargetEigenvector_bound ha hb
  have hdim : Tendsto (fun r => ns r+1) atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_succ _) hns
  let f (r k:ℕ) : ℂ := (1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (ns r+1) k/2:ℝ):ℂ)*(w r:ℂ))⁻¹*
    (scaledTargetEigenvector a b ha hb (ns r) (i r) k:ℂ)^2
  let g (k:ℕ) : ℂ := (1+((jacobi.Bessel.edgeValue a ha k/2:ℝ):ℂ)*(w0:ℂ))⁻¹*(spectralProfile a ha k t:ℂ)
  have hf : ∀ᶠr:ℕ in atTop,∀k:ℕ,‖f r k‖≤C*B^2 := by
    filter_upwards [hns.eventually hden,hns.eventually hvec] with r hr hv k
    dsimp only [f]
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (hr k (w r) (w r).property).2.1
      ((sq_le_sq₀ (abs_nonneg _) hB.le).mpr (hv (i r) k)) (sq_nonneg _) hC.le
  have hp (k:ℕ) : Tendsto (fun r => f r k) atTop (𝓝 (g k)) := by
    have hweight := (jacobi.Jacobi.finiteLambdaAt_tendsto ha hb k).comp hdim
    have hwc := continuous_subtype_val.continuousAt.tendsto.comp hw
    have harg := (tendsto_const_nhds (x:=(1:ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hweight.div_const 2)).mul hwc)
    have hhalf : jacobi.Bessel.edgeValue a ha k/2=1/ jacobi.Bessel.sigma a ha k := by rw [jacobi.Bessel.edgeValue]; ring
    have hne := slit_denominator_ne
      (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)) (inverse_sigma_mem a ha k) (hsub w0.property)
    rw [← hhalf] at hne
    have hv := (target_eigenvector_full_limit ha hb k ns hns i hit).pow 2
    rw [fullWaveMap_sq] at hv
    simpa only [f,g,Function.comp_def,Complex.ofReal_pow,scaledTargetEigenvector] using
      (harg.inv₀ hne).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hv)
  have hh := weighted_series_normed (r:=fun r k => jacobi.Jacobi.finiteLambdaAt a b ha hb (ns r+1) k)
    (L:= jacobi.Bessel.edgeValue a ha) (f:=f) (g:=g)
    (fun r => jacobi.Jacobi.finiteLambdaAt_summable ha hb (ns r+1)) (jacobi.Bessel.edgeValue_summable ha)
    ((jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).comp hdim) hf hp
  have he (r:ℕ) : (∑'k,jacobi.Jacobi.finiteLambdaAt a b ha hb (ns r+1) k • f r k)=
      finiteShiftedDiagonal a b ha hb (ns r) (i r) (w r) := by
    apply tsum_congr
    intro k
    change (jacobi.Jacobi.finiteLambdaAt a b ha hb (ns r+1) k:ℂ)*f r k=_
    simp only [f,finiteShiftedEdge,resolventTransform,mul_assoc]
  have he0 : (∑'k,jacobi.Bessel.edgeValue a ha k • g k)=shiftedProfile a ha t w0 := by
    apply tsum_congr
    intro k
    rw [shiftedProfileTerm,shiftedEdge_transform a ha k (hsub w0.property)]
    change (jacobi.Bessel.edgeValue a ha k:ℂ)*g k=_
    simp only [g,resolventTransform,mul_assoc]
  simpa only [he,he0] using hh

end
end jacobi.EdgeResolvent
