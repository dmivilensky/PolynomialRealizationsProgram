import jacobi.Support.MovingEdge
import jacobi.Comparison.GramSummands
import jacobi.Comparison.TargetWeightLimit

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Every actual fixed right-edge Gram summand converges to the original
GL kernel summand along arbitrary moving physical matrix indices.
The original finite probabilities, corrected support polynomials and
their exact Gamma amplitudes are retained and canceled explicitly.
Use: gramSummandAt_limit and the full spectral half-row limit state the actual finite-to-infinite comparison on one fixed spectral index space.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter Polynomial jacobi.Support jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The original finite Gram summand on scalar spectral indices, extended by zero outside the original dimension.
Use: gramSummandAt_limit and the full spectral half-row limit state the actual finite-to-infinite comparison on one fixed spectral index space.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def gramSummandAt (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) (k:ℕ) : ℝ :=
  if hk:k<n+1 then gramSummand a b ha hb n i j ⟨k,hk⟩ else 0

/-- The original Gram product has exactly its degree-scaled weight times its two degree-scaled polynomial values.
Use: gramSummandAt_limit combines the actual independent probability and polynomial limits and cancels their same genuine powers of the original degree.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the three positive-base degree powers add to one; factor the genuine scalar product before using that exact identity. -/
theorem edge_product_scale {x:ℝ} (hx:0<x) (g w p q:ℝ) :
    x*w*p*q=(x^(1+2*g)*w)*(x^(-g)*p)*(x^(-g)*q) := by
  have hp : x^(1+2*g)*x^(-g)*x^(-g)=x := by
    rw [← rpow_add hx,← rpow_add hx,show 1+2*g+-g+-g=(1:ℝ) by ring,rpow_one]
  calc
    _ = (x^(1+2*g)*x^(-g)*x^(-g))*(w*p*q) := by rw [hp]; ring
    _ = _ := by ring

/-- Every original fixed right-edge Gram summand has the true original GL summand limit along arbitrary moving physical half-chain row and column indices.
Use: the full growing right spectral half-row converges to the actual source kernel F, using gramSummand_bound for the remaining spectral tail. Reflection then gives the opposite kernel and the actual two-edge Gram limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the actual target and support probabilities have their exact independent norming limits. The genuine corrected support polynomials have their proved moving-index limits at the actual target and support nodes. Their common Gamma amplitude square cancels the actual weight normalization, giving exactly the source kernelTerm. Finally convert from the degree to the true matrix-size normalization. -/
theorem gramSummandAt_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i j:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    (hj:∀ᶠn:ℕ in atTop,2*(j n).val≤ns n+1) {t s:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n:ℕ => ((ns n:ℝ)+1)*gramSummandAt a b ha hb (ns n) (i n) (j n) k) atTop
      (𝓝 (jacobi.GelfandLevitan.kernelTerm a ha k t s)) := by
  -- All four polynomial limits use the same original support family and the actual two source spectra.
  have hti := supportPolynomial_target_limit ha hb k ns hns i hi ht hit
  have htj := supportPolynomial_target_limit ha hb k ns hns j hj hs hjs
  have hsi := supportPolynomial_model_limit ha hb k ns hns i hi ht hit
  have hsj := supportPolynomial_model_limit ha hb k ns hns j hj hs hjs
  have hlim := ((((targetWeight_degree_limit ha hb k).comp hns).mul hti).mul htj).sub
    ((((fixedWeight_limit ha hb k).comp hns).mul hsi).mul hsj)
  let K : ℝ := topConstant a b*π^gamma a
  have hK : K^2=topAmplitudeSquare a b := by
    dsimp only [K]
    rw [mul_pow,show (π^gamma a)^2=π^(2*gamma a) by
      rw [pow_two,← rpow_add pi_pos]; congr 1; ring]
    exact topConstant_amplitude ha hb
  have hA := (topAmplitudeSquare_pos ha hb).ne'
  have hn := (norming_pos ha k).ne'
  have hv : ((normingRatio a ha k/norming a k)/topAmplitudeSquare a b)*
      (K*realSolution a (jacobi.Bessel.sigma a ha k) t)*(K*realSolution a (jacobi.Bessel.sigma a ha k) s)-
      (topAmplitudeSquare a b*norming a k)⁻¹*
      (K*realSolution a (eigenvalue a k) t)*(K*realSolution a (eigenvalue a k) s)=
      jacobi.GelfandLevitan.kernelTerm a ha k t s := by
    calc
      _ = (K^2/topAmplitudeSquare a b)*
          ((normingRatio a ha k*realSolution a (jacobi.Bessel.sigma a ha k) t*
            realSolution a (jacobi.Bessel.sigma a ha k) s-
            realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s)/norming a k) := by
        field_simp [hA,hn]
      _ = _ := by rw [hK,div_self hA,one_mul]; rfl
  rw [show topConstant a b*π^gamma a=K from rfl] at hlim
  rw [hv] at hlim
  have hdegree : Tendsto (fun n:ℕ => (ns n:ℝ)*gramSummandAt a b ha hb (ns n) (i n) (j n) k) atTop
      (𝓝 (jacobi.GelfandLevitan.kernelTerm a ha k t s)) := by
    apply (tendsto_congr' ?_).mpr hlim
    filter_upwards [hns.eventually_ge_atTop k,hns.eventually_gt_atTop 0] with n hnk hnpos
    have hk : k<ns n+1 := by omega
    have hnR : (0:ℝ)<ns n := by exact_mod_cast hnpos
    simp only [Function.comp_def,gramSummandAt,dite_eq_left hk,gramSummand,targetWeight,naturalWeight,
      cosAngleAt_node a b ha hb hk]
    rw [mul_sub]
    conv_lhs => simp only [← mul_assoc]
    rw [edge_product_scale hnR (gamma a),edge_product_scale hnR (gamma a)]
    rfl
  have hratio := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hns).const_add 1
  simp only [add_zero] at hratio
  have h := hratio.mul hdegree
  simp only [one_mul] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [hns.eventually_gt_atTop 0] with n hnpos
  have hnR : (ns n:ℝ)≠0 := by exact_mod_cast hnpos.ne'
  dsimp only [Function.comp_def]
  field_simp [hnR]

end
end jacobi.Comparison
