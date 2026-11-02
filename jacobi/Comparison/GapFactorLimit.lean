import jacobi.Comparison.WeightLogFactors
import jacobi.Support.NodeLimit

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The literal finite gap factors converge to the original norming factors
at the same edge and to one at the opposite edge. The full source
finite-to-infinite product argument uses these limits together with the
independently proved uniform summable folded majorant.
Use: gapFactorAt_tendsto and gapFactorAt_reflected_tendsto state fixed-index limits on an ordinary sequence space before the actual finite products are summed.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The original finite gap factor on scalar indices, with the omitted diagonal set to one.
Use: gapFactorAt_tendsto and gapFactorAt_reflected_tendsto state fixed-index limits on an ordinary sequence space before the actual finite products are summed.
Article: jacobi, Proposition C.3.
The original node is represented by cos(finiteAngleAt); only valid indices enter the finite-product identity. Values at other indices are irrelevant to that identity. -/
def gapFactorAt (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k j:ℕ) : ℝ :=
  if j=k then 1 else |modelNode a b (n+1) k-modelNode a b (n+1) j|/
    |cos (finiteAngleAt a b ha hb (n+1) k)-cos (finiteAngleAt a b ha hb (n+1) j)|

/-- The scalar cosine-angle representative is exactly the original finite Jacobi node whenever its index is valid.
Use: gapFactorAt_log_sum and the two-edge majorants concern the same original finite target nodes as the canonical target matrix.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the padded angle is the true original node angle at every valid index; the proved inverse-cosine identity recovers that same original node. -/
theorem cosAngleAt_node (a b:ℝ) (ha:-1<a) (hb:-1<b) {N k:ℕ} (hk:k<N) :
    cos (finiteAngleAt a b ha hb N k)=(nodes a b ha hb N).value ⟨k,hk⟩ := by
  rw [finiteAngleAt_eq ha hb hk]
  exact (angle_properties ha hb ⟨k,hk⟩).2

/-- The logarithm of the actual original relative product is the full finite sum of the scalar gap logarithms, with its zero diagonal included.
Use: the full fixed-index product limit can split the original spectrum into its two half-rows without carrying an erased diagonal through dominated convergence.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the original erased-product logarithm identity is already proved. At every valid scalar index the cosine representative is the actual node; the inserted diagonal has logarithm zero. -/
theorem gapFactorAt_log_sum (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    log (relativeGapProduct a b ha hb n k)=∑j:Fin (n+1),log (gapFactorAt a b ha hb n k.val j.val) := by
  -- The inserted diagonal is exactly log(1)=0; every retained scalar index is its genuine finite node.
  rw [relativeGapProduct_log_sum]
  have he : (∑j∈univ.erase k,log (gapFactorAt a b ha hb n k.val j.val))=
      ∑j:Fin (n+1),log (gapFactorAt a b ha hb n k.val j.val) := by
    have h := sum_erase_add univ (fun j:Fin (n+1) => log (gapFactorAt a b ha hb n k.val j.val)) (mem_univ k)
    simpa only [gapFactorAt,ite_true,log_one,add_zero] using h
  rw [← he]
  apply sum_congr rfl
  intro j hj
  have hne : j.val≠k.val := fun h => (mem_erase.mp hj).1 (Fin.ext h)
  rw [gapFactorAt,ite_eq_right hne,cosAngleAt_node a b ha hb k.isLt,cosAngleAt_node a b ha hb j.isLt]

/-- Every fixed literal original support node tends to the right endpoint.
Use: gapFactorAt_reflected_tendsto proves that factors connecting opposite spectral edges tend to one in the same original finite product.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the exact original grid angle tends to zero, its affine scale tends to one and its affine shift tends to zero. -/
theorem modelNode_tendsto_one (a b:ℝ) (k:ℕ) :
    Tendsto (fun n:ℕ => modelNode a b (n+1) k) atTop (𝓝 1) := by
  have hangle : Tendsto (fun n:ℕ => modelAngle a b n k) atTop (𝓝 0) :=
    (frequency_tendsto a b).const_div_atTop _
  have hcos := continuous_cos.continuousAt.tendsto.comp hangle
  have ht := ((modelScale_tendsto a b).mul hcos).add (modelShift_tendsto a b)
  simp only [cos_zero,mul_one,add_zero] at ht
  exact ht.comp (tendsto_add_atTop_nat 1)

/-- Every fixed original finite gap factor at the right edge converges to its genuine original reference norming factor.
Use: the full product limit obtains the actual rho_k after dominated convergence of these same logarithms.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: multiply both original node gaps by the same genuine positive 2*N^2. Their actual squared-distance limits are the independently proved reference and Bessel eigenvalues. Divide the two nonzero limiting gaps; both spectra have the same strict order, so their absolute-gap quotient equals the positive original norming factor. -/
theorem gapFactorAt_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k j:ℕ) :
    Tendsto (fun n:ℕ => gapFactorAt a b ha hb n k j) atTop (𝓝 (normingFactor a ha k j)) := by
  -- The two source edge energies are retained before taking the ratio; no assumed weight limit is used.
  by_cases h:j=k
  · subst j
    simpa only [gapFactorAt,normingFactor,ite_true] using (tendsto_const_nhds (x:=(1:ℝ)))
  have hσ : jacobi.Bessel.sigma a ha j- jacobi.Bessel.sigma a ha k≠0 :=
    sub_ne_zero.mpr (fun he => h ((jacobi.Bessel.sigma_strictMono ha).injective he))
  have hcos (l:ℕ) := (cosine_distance_tendsto ha hb l).const_mul 2
  simp only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] at hcos
  have ht := (((jacobi.Support.supportNode_limit ha hb j).sub (jacobi.Support.supportNode_limit ha hb k)).abs).div
    (((hcos j).sub (hcos k)).abs) (abs_ne_zero.mpr hσ)
  have hlimit : |eigenvalue a j-eigenvalue a k| / |jacobi.Bessel.sigma a ha j- jacobi.Bessel.sigma a ha k|=
      normingFactor a ha k j := by
    have he : normingFactor a ha k j=(eigenvalue a j-eigenvalue a k)/(jacobi.Bessel.sigma a ha j- jacobi.Bessel.sigma a ha k) := by
      rw [normingFactor,ite_eq_right h]
    rw [← abs_div,← he]
    exact abs_of_pos (normingFactor_pos ha k j)
  rw [hlimit] at ht
  apply (ht.comp (tendsto_add_atTop_nat 1)).congr'
  filter_upwards [(frequency_tendsto a b).comp (tendsto_add_atTop_nat 1) |>.eventually (eventually_gt_atTop (0:ℝ))] with n hn
  rw [gapFactorAt,ite_eq_right h]
  have h₁ : 2*(frequency a b (n+1))^2*(1-modelNode a b (n+1) j)-2*(frequency a b (n+1))^2*(1-modelNode a b (n+1) k)=
      (2*(frequency a b (n+1))^2)*(modelNode a b (n+1) k-modelNode a b (n+1) j) := by ring
  have h₂ : 2*((frequency a b (n+1))^2*(1-cos (finiteAngleAt a b ha hb (n+1) j)))-
      2*((frequency a b (n+1))^2*(1-cos (finiteAngleAt a b ha hb (n+1) k)))=
      (2*(frequency a b (n+1))^2)*(cos (finiteAngleAt a b ha hb (n+1) k)-cos (finiteAngleAt a b ha hb (n+1) j)) := by ring
  change |2*(frequency a b (n+1))^2*(1-modelNode a b (n+1) j)-2*(frequency a b (n+1))^2*(1-modelNode a b (n+1) k)| /
    |2*((frequency a b (n+1))^2*(1-cos (finiteAngleAt a b ha hb (n+1) j)))-
      2*((frequency a b (n+1))^2*(1-cos (finiteAngleAt a b ha hb (n+1) k)))|= _
  rw [h₁,h₂]
  simp only [abs_mul]
  exact mul_div_mul_left (c:=|(2:ℝ)| * |(frequency a b (n+1))^2|) _ _ (by positivity)

/-- Factors connecting a fixed right index to a fixed reflected left index tend to one in the actual original finite product.
Use: the reflected half-row contributes zero to the limiting logarithm, so the full normalized right-edge probability has precisely rho_alpha, without a spurious beta-dependent constant.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: exact model and target node reflection writes each gap as the sum of a fixed right node for the original parameters and a fixed right node for the exchanged parameters. Both actual node families tend to one. Thus numerator and denominator tend to two, and their positive absolute-gap quotient tends to one. -/
theorem gapFactorAt_reflected_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k j:ℕ) :
    Tendsto (fun n:ℕ => gapFactorAt a b ha hb n k (n-j)) atTop (𝓝 1) := by
  -- Both original endpoint parameters remain in the finite factors until the true opposite-edge limit is taken.
  have hcos (c d:ℝ) (hc:-1<c) (hd:-1<d) (l:ℕ) :
      Tendsto (fun n:ℕ => cos (finiteAngleAt c d hc hd (n+1) l)) atTop (𝓝 1) := by
    simpa only [cos_zero,Function.comp_def] using continuous_cos.continuousAt.tendsto.comp
      ((finiteAngleAt_tendsto_zero hc hd l).comp (tendsto_add_atTop_nat 1))
  have ht := (((modelNode_tendsto_one a b k).add (modelNode_tendsto_one b a j)).abs).div
    (((hcos a b ha hb k).add (hcos b a hb ha j)).abs) (by norm_num : |(1:ℝ)+1|≠0)
  norm_num only [one_add_one_eq_two,abs_of_pos (by norm_num : (0:ℝ)<2),div_self (by norm_num : (2:ℝ)≠0)] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (k+2*j+1)] with n hn
  have hj : j<n+1 := by omega
  have hnj : n-j<n+1 := by omega
  have hne : n-j≠k := by omega
  have hm := modelNode_reflection ha hb (n:=n+1) hj
  have hm' : modelNode a b (n+1) (n-j)= -modelNode b a (n+1) j := by simpa only [Nat.add_sub_cancel] using hm
  have hc : cos (finiteAngleAt a b ha hb (n+1) (n-j))= -cos (finiteAngleAt b a hb ha (n+1) j) := by
    rw [cosAngleAt_node a b ha hb hnj,cosAngleAt_node b a hb ha hj]
    have hi : (⟨n-j,hnj⟩:Fin (n+1))=(⟨j,hj⟩:Fin (n+1)).rev := by apply Fin.ext; simp only [Fin.val_rev]; omega
    rw [hi]
    exact nodes_reflection ha hb ⟨j,hj⟩
  simp only [gapFactorAt,ite_eq_right hne,hm',hc,sub_neg_eq_add]
  rfl

end
end jacobi.Comparison
