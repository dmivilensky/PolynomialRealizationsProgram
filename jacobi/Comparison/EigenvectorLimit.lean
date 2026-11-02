import jacobi.Comparison.TargetPolynomialLimit
import jacobi.Comparison.TargetWeightLimit
import jacobi.Analysis.SqrtNormalization
import jacobi.GelfandLevitan.FullWaveEndpoint
import jacobi.Comparison.EigenvectorBounds

/-!
Article: jacobi, Proposition C.3.
The signed eigenvectors of the actual persymmetric target matrix have
the original transformed-wave limit with its exact positive norming
weight. The true finite dimension is N=n+1 throughout the final limit.
Use: the signed moving-row and floor-row limits use a fixed spectral index without a dimension-dependent index proof in the limit filter.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Support jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- The actual target eigenvector entry at a scalar spectral index,
with zero padding only outside its genuine finite spectral dimension.
Use: the signed moving-row and floor-row limits use a fixed spectral
index without a dimension-dependent index proof in the limit filter.
Article: jacobi, Proposition C.3.
-/
def targetEigenvectorEntry (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (k:ℕ) : ℝ :=
  if hk:k<n+1 then (targetMeasure a b ha hb n).reconstructedBasis.Q i ⟨k,hk⟩ else 0

/-- The genuine eigenvector amplitude is the printed positive target
norming factor after cancellation of the original Gamma amplitude.
Use: target_eigenvector_degree_limit identifies its limit with the
same normalized continuum wave used by the actual H_alpha basis.
Article: jacobi, Proposition C.3.
Proof: the original amplitude square is exactly the independently
proved Gamma amplitude; positivity fixes the square-root branch. -/
theorem target_eigenvector_amplitude {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    sqrt ((normingRatio a ha k/norming a k)/topAmplitudeSquare a b)*
      (topConstant a b*π^gamma a)=targetWaveScale a ha k := by
  have hA : 0<topConstant a b*π^gamma a :=
    mul_pos (topConstant_pos ha hb) (rpow_pos_of_pos pi_pos _)
  have hAA : (topConstant a b*π^gamma a)^2=topAmplitudeSquare a b := by
    rw [mul_pow,show (π^gamma a)^2=π^(2*gamma a) by
      rw [pow_two,← rpow_add pi_pos]; congr 1; ring]
    exact topConstant_amplitude ha hb
  rw [← hAA,sqrt_amplitude_cancel hA (div_nonneg
    (normingRatio_properties ha k).2.le (norming_pos ha k).le),targetWaveScale_eq_sqrt]

/-- The actual signed target eigenvector has its genuine edge limit
in the degree normalization along every cofinal moving half row.
Use: target_eigenvector_half_limit passes to the true matrix dimension
and supplies the original signed limit of Appendix C.4.
Article: jacobi, Proposition C.3.
Proof: multiply the two genuine source limits. The original powers
cancel exactly at every positive degree; no absolute value or square
of the polynomial is taken. The exact positive amplitude cancellation
identifies the same signed normalized transformed solution. -/
theorem target_eigenvector_degree_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    (hi:∀ᶠr:ℕ in atTop,2*(i r).val≤ns r+1)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun r => sqrt (ns r:ℝ)*targetEigenvectorEntry a b ha hb (ns r) (i r) k)
      atTop (𝓝 (targetWaveScale a ha k*realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) ⟨t,ht⟩)) := by
  -- Both limits concern the original target measure and its original Schur polynomials.
  have hw := ((targetWeight_degree_limit ha hb k).comp hns).sqrt
  have hp := targetPolynomial_edge_limit ha hb k ns hns i hi ht hit
  have hh := hw.mul hp
  rw [← mul_assoc,target_eigenvector_amplitude ha hb k] at hh
  apply hh.congr'
  filter_upwards [hns.eventually_gt_atTop 0,hns.eventually_ge_atTop k] with r hr hk
  have hn : (0:ℝ)<ns r := by exact_mod_cast hr
  have hkn : k<ns r+1 := by omega
  simp only [Function.comp_def,targetEigenvectorEntry,targetWeight,dite_eq_left hkn,targetEdgeValue]
  rw [← mul_assoc,sqrt_weight_power hn,cosAngleAt_node a b ha hb hkn,
    target_eigenvector_polynomial,mul_assoc]

/-- The full signed original eigenvector limit holds in the true
matrix-size normalization on every cofinal moving physical half row,
including the genuine middle row and its zero odd-parity limit.
Use: the full floor-row theorem gives Theorem 2.1; squared limits
and spectral summation yield Theorem 2.1 and the Green limits in Theorem 2.1.
Article: jacobi, Proposition C.3.
Proof: the actual degree-normalized signed limit is already proved.
The true dimension/degree ratio tends to one, and its positive square
root converts the exact finite normalization without changing the limit. -/
theorem target_eigenvector_half_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    (hi:∀ᶠr:ℕ in atTop,2*(i r).val≤ns r+1)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 t)) :
    Tendsto (fun r => sqrt ((ns r:ℝ)+1)*targetEigenvectorEntry a b ha hb (ns r) (i r) k)
      atTop (𝓝 (targetWaveScale a ha k*realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) ⟨t,ht⟩)) := by
  have hd := target_eigenvector_degree_limit ha hb k ns hns i hi ht (size_to_degree_mesh hns hit)
  have hr := (successor_ratio_tendsto hns).sqrt
  simp only [sqrt_one] at hr
  have hh := hr.mul hd
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hns.eventually_gt_atTop 0] with r hr
  rw [← mul_assoc,sqrt_ratio_mul (by positivity) (by exact_mod_cast hr)]

/-- The original signed physical reflection remains exact under the
scalar spectral padding used in all fixed-edge limits.
Use: target_eigenvector_full_limit extends the same actual signed
half-chain limit to the reflected physical half without any new parity
or eigenvector choice assumption.
Article: jacobi, Proposition C.3.
Proof: genuine indices use the actual persymmetric parity; outside
the finite spectral dimension both padded entries are zero. -/
theorem targetEigenvectorEntry_parity (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (k:ℕ) :
    targetEigenvectorEntry a b ha hb n i.rev k=(-1:ℝ)^k*targetEigenvectorEntry a b ha hb n i k := by
  by_cases hk:k<n+1
  · simp only [targetEigenvectorEntry,dite_eq_left hk]
    exact target_eigenvector_parity a b ha hb n i ⟨k,hk⟩
  · simp only [targetEigenvectorEntry,dite_eq_right hk,mul_zero]

end
end jacobi.Comparison
