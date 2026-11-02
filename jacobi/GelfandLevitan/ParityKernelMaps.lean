import jacobi.GelfandLevitan.FiniteKernelMaps
import jacobi.GelfandLevitan.HalfReferenceCompleteness
import jacobi.GelfandLevitan.ParitySplitting

/-!
Article: jacobi, Proposition C.2.
Each original parity kernel subseries sums to F/2 in the actual uniform
function norm. Thus the pointwise contour parity identity really does
justify integration against arbitrary physical L2 functions.
Use: all parity subsequences and their genuine signed sum converge uniformly in ParityKernelMaps.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
attribute [local irreducible] kernel kernelTerm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual source kernel summands are summable in the compact-domain uniform norm.
Use: all parity subsequences and their genuine signed sum converge uniformly in ParityKernelMaps.
Article: jacobi, Proposition C.2.
Proof: the full-index inverse-square bound controls each actual continuous-kernel supremum norm and is summable. -/
theorem kernelTermMap_norm_summable (a : ℝ) (ha : -1<a) :
    Summable (fun k => ‖kernelTermMap a ha k‖) := by
  obtain ⟨C,hC,hbound⟩ := kernelTerm_uniform_bound a ha
  have hM : Summable (fun k:ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  apply hM.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  apply ((kernelTermMap a ha k).norm_le (by positivity)).mpr
  exact fun p => hbound k _ (halfTime_mem p.1) _ (halfTime_mem p.2)

/-- The original kernel maps are summable in their genuine function norm.
Use: kernelTermMap_hasSum and its parity subseries retain the actual original F summands.
Article: jacobi, Proposition C.2.
Proof: the independently proved absolute norm summability gives convergence in the complete continuous-function space. -/
theorem kernelTermMap_summable (a : ℝ) (ha : -1<a) : Summable (kernelTermMap a ha) :=
  (kernelTermMap_norm_summable a ha).of_norm

/-- The actual continuous source kernel summands have their original F as their genuine uniform-norm sum.
Use: identifies the total of the even and odd uniform subseries with the unchanged original kernel.
Article: jacobi, Proposition C.2.
Proof: the independently proved uniform convergence of the original finite prefixes and summability give the same unique limit. -/
theorem kernelTermMap_hasSum (a : ℝ) (ha : -1<a) :
    HasSum (kernelTermMap a ha) (kernelMap a ha) := by
  have hs := (kernelTermMap_summable a ha).hasSum
  have he : (∑' k,kernelTermMap a ha k)=kernelMap a ha :=
    tendsto_nhds_unique hs.tendsto_sum_nat (finiteKernelMap_limit a ha)
  rwa [he] at hs

/-- The actual alternating source kernel series has uniform-norm sum zero.
Use: proves that both genuine parity subseries have sum F/2, with no extra operator-parity hypothesis.
Article: jacobi, Proposition C.2.
Proof: the signed actual terms have the same summable uniform norms. Evaluate their genuine norm sum at any original point, and use the already proved original contour parity sum there. -/
theorem signed_kernelTermMap_hasSum (a : ℝ) (ha : -1<a) :
    HasSum (fun k => (-1:ℝ)^k • kernelTermMap a ha k) 0 := by
  -- Evaluation commutes with the actual norm sum; pointwise parity identifies that same sum everywhere.
  have hs : Summable (fun k => (-1:ℝ)^k • kernelTermMap a ha k) :=
    (kernelTermMap_norm_summable a ha).of_norm_bounded (fun k => by
      rw [norm_smul,Real.norm_eq_abs,abs_neg_one_pow,one_mul])
  have hz : (∑' k,(-1:ℝ)^k • kernelTermMap a ha k)=0 := by
    apply ContinuousMap.ext
    intro p
    have h := (ContinuousMap.evalCLM ℝ p).hasSum hs.hasSum
    have hp := parity_splitting ha (halfTime_mem p.1) (halfTime_mem p.2)
    change HasSum (fun k => (-1:ℝ)^k*kernelTerm a ha k (halfTime p.1) (halfTime p.2))
      ((∑' k,(-1:ℝ)^k • kernelTermMap a ha k) p) at h
    exact h.unique hp
  have h := hs.hasSum
  rwa [hz] at h

/-- Both actual source parity kernel series converge uniformly to one half of the original F.
Use: kernelPairing transfers this genuine uniform sum to the two original spectral forms in the transformed tight-frame calculation.
Article: jacobi, Proposition C.2.
Proof: the even and odd norm-convergent subseries add to F. Their difference is the proved zero alternating series, so each is exactly F/2. -/
theorem parity_kernelTermMap_hasSum (a : ℝ) (ha : -1<a) (p : Fin 2) :
    HasSum (fun k => kernelTermMap a ha (parityIndex p k)) ((1/2:ℝ) • kernelMap a ha) := by
  -- The two scalar identities are lifted in the original continuous-function space, before any L2 pairing.
  have he : Summable (fun k => kernelTermMap a ha (2*k)) :=
    (kernelTermMap_summable a ha).comp_injective (fun _ _ h => by omega)
  have ho : Summable (fun k => kernelTermMap a ha (2*k+1)) :=
    (kernelTermMap_summable a ha).comp_injective (fun _ _ h => by omega)
  let E := ∑' k,kernelTermMap a ha (2*k)
  let O := ∑' k,kernelTermMap a ha (2*k+1)
  have hsum : E+O=kernelMap a ha :=
    (he.hasSum.even_add_odd ho.hasSum).unique (kernelTermMap_hasSum a ha)
  have hes : HasSum (fun k => (-1:ℝ)^(2*k) • kernelTermMap a ha (2*k)) E := by
    simpa only [pow_mul,neg_one_sq,one_pow,one_smul] using he.hasSum
  have hos : HasSum (fun k => (-1:ℝ)^(2*k+1) • kernelTermMap a ha (2*k+1)) (-O) := by
    simpa only [pow_add,pow_mul,neg_one_sq,one_pow,pow_one,one_mul,neg_one_smul] using ho.hasSum.neg
  have hdiff : E-O=0 := by
    simpa only [sub_eq_add_neg] using
      (hes.even_add_odd hos).unique (signed_kernelTermMap_hasSum a ha)
  have heq : E=O := sub_eq_zero.mp hdiff
  have hE : E=(1/2:ℝ) • kernelMap a ha := by
    rw [← hsum,← heq,smul_add,← add_smul]
    norm_num
  have hO : O=(1/2:ℝ) • kernelMap a ha := heq.symm.trans hE
  fin_cases p
  · change HasSum (fun k => kernelTermMap a ha (2*k+0)) _
    have h : HasSum (fun k => kernelTermMap a ha (2*k)) E := he.hasSum
    rw [hE] at h
    simpa only [Nat.add_zero] using h
  · change HasSum (fun k => kernelTermMap a ha (2*k+1)) _
    have h : HasSum (fun k => kernelTermMap a ha (2*k+1)) O := ho.hasSum
    rwa [hO] at h

end
end jacobi.GelfandLevitan
