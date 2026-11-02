import jacobi.Applications.PaddedDescent

/-!
The final comparison of all three-term and block realizations with the
original Nesterov endpoint channel. Every numerator is an actual full
finite-fibre optimum; the denominator is the original two-memory method.
The nonnegative extended formulation retains the whole fibre and is
equivalent to ordinary finite ratios. The symmetric ratios converge to two.
Article: jacobi, Corollary 5.7.
Article role: the actual block and full-class ratios and the explicit strict deficit from two.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The original method's actual squared channel, normalized by its
positive full horizon. It is the common comparison denominator.
Article: jacobi, Corollary 5.7.
-/
def nesterovEndpointValue (b : ℝ) (n : ℕ) : ℝ :=
  ((nesterovMethod b).kernelNorm (n+1) 0 0)^2/((n+1:ℕ):ℝ)^3

/-- The original denominator has the proved strictly positive limit.
Article: jacobi, Corollary 5.7.
-/
theorem nesterovEndpointValue_limit {b : ℝ} (hb : -1<b) :
    Tendsto (nesterovEndpointValue b) atTop (𝓝 (standardEnergy (b/2)/4)) :=
  (standardEnergy_endpoint_limit hb).comp (tendsto_add_atTop_nat 1)

/-- The actual full-class optimal ratio, with no selected realization.
Article: jacobi, Corollary 5.7.
-/
def nesterovClosedRatio (b : ℝ) (hb : -1<b) (n : ℕ) : ℝ≥0∞ :=
  closedEndpointMinimum (nesterovClosedNodes (b/2) (by linarith) n)/
    ENNReal.ofReal (nesterovEndpointValue b n)

/-- The actual factor-block class ratio with the same full horizon.
Article: jacobi, Corollary 5.7.
-/
def nesterovBlockRatio (b : ℝ) (hb : -1<b) (n : ℕ) : ℝ≥0∞ :=
  nesterovBlockMinimum (b/2) (by linarith) n/ENNReal.ofReal (nesterovEndpointValue b n)

/-- Dividing a full lower limit by an actually convergent positive
denominator preserves the lower bound, including extended numerators.
Article: jacobi, Corollary 5.7.
-/
theorem endpoint_ratio_lower (A : ℕ → ℝ≥0∞) (D : ℕ → ℝ) {d : ℝ}
    (hD : Tendsto D atTop (𝓝 d)) {L : ℝ≥0∞} (hA : L≤liminf A atTop) :
    L/ENNReal.ofReal d≤liminf (fun n => A n/ENNReal.ofReal (D n)) atTop := by
  have hi := tendsto_inv_iff.mpr (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hD)
  simp only [Function.comp_def] at hi
  have h := ENNReal.le_liminf_mul (u := A) (v := fun n => (ENNReal.ofReal (D n))⁻¹) (f := atTop)
  rw [hi.liminf_eq] at h
  simpa only [Pi.mul_def,div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right hA bot_le).trans h

/-- A convergent real majorant bounds the upper ratio for the actual
extended optimum. Positivity is required only of the limiting denominator.
Article: jacobi, Corollary 5.7.
-/
theorem endpoint_ratio_upper (A : ℕ → ℝ≥0∞) (R D : ℕ → ℝ) {r d : ℝ}
    (hR : Tendsto R atTop (𝓝 r)) (hD : Tendsto D atTop (𝓝 d)) (hd : 0<d)
    (hA : ∀ᶠ n in atTop,A n≤ENNReal.ofReal (R n)) :
    limsup (fun n => A n/ENNReal.ofReal (D n)) atTop≤ENNReal.ofReal (r/d) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hR.div hD hd.ne')
  have hb : ∀ᶠ n in atTop,A n/ENNReal.ofReal (D n)≤ENNReal.ofReal (R n/D n) := by
    filter_upwards [hA,hD.eventually (Ioi_mem_nhds hd)] with n hn hdn
    rw [ENNReal.ofReal_div_of_pos hdn]
    exact mul_le_mul_of_nonneg_right hn bot_le
  exact (limsup_le_limsup (f := atTop) hb).trans_eq hlim.limsup_eq

/-- The actual parity-selected flowed block majorant, at every horizon.
Article: jacobi, Corollary 5.7.
-/
def nesterovFlowMajorant (a : ℝ) (ha : -(1/2:ℝ)<a) (n : ℕ) : ℝ :=
  paddedFlowMajorant a ha (n%2) (n/2-1)

/-- Both parities give the same proved scalar majorant limit.
Article: jacobi, Corollary 5.7.
-/
theorem nesterovFlowMajorant_limit {a : ℝ} (ha : -(1/2:ℝ)<a) :
    Tendsto (nesterovFlowMajorant a ha) atTop (𝓝 (descentTaylorValue a/2)) := by
  have hm : Tendsto (fun n : ℕ => n/2-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (le_of_eq (map_div_atTop_eq_nat 2 (by omega)))
  exact tendsto_parity_choice (fun e n => paddedFlowMajorant a ha e (n/2-1))
    (fun n => n%2) (fun _ => by omega)
    ((paddedFlowMajorant_limit ha 0).comp hm) ((paddedFlowMajorant_limit ha 1).comp hm)

/-- The printed explicit deficit from two is the exact rational upper
comparison obtained from the energy improvement.
Article: jacobi, Corollary 5.7.
-/
theorem descent_ratio_identity {b : ℝ} (hb : -1<b) :
    ((standardEnergy (b/2)-descentGap (b/2))/2)/(standardEnergy (b/2)/4)=
      2-12*(b-1)^2/(25*(b+5)^2*(2*b+5)^2*(3*b+5)^2) := by
  rw [← descentGap_ratio hb]
  have hC := (standardEnergy_pos (by linarith : -(1/2:ℝ)<b/2)).ne'
  field_simp
  ring


/-- The printed Young lower ratio, using the original actual Bessel
second-moment calibration rather than an independent numeric bound.
Article: jacobi, Corollary 5.7.
-/
def nesterovYoungRatio (b : ℝ) : ℝ :=
  2*jacobi.Parameter.youngLower (b/2)/standardEnergy (b/2)

/-- The explicit Young ratio lies below the retained homogeneous lower
comparison. This completes the first inequality of the ratio sandwich.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_young_ratio_lower {b : ℝ} (hb : -1<b) :
    ENNReal.ofReal (nesterovYoungRatio b)≤
      ((1/2:ℝ≥0∞)*homogeneousLowerConstant
        (jacobi.Bessel.edgeSpectrum (b/2) (by linarith)))/ENNReal.ofReal (standardEnergy (b/2)/4) := by
  have ha : -(1/2:ℝ)<b/2 := by linarith
  have hC := standardEnergy_pos ha
  have h := young_le_homogeneous (jacobi.Bessel.edgeSpectrum (b/2) (by linarith))
  rw [← jacobi.Parameter.youngLower_spectral] at h
  have hmul := mul_le_mul_of_nonneg_left h (show (0:ℝ≥0∞)≤1/2 from bot_le)
  have he : ENNReal.ofReal (nesterovYoungRatio b)=
      ((1/2:ℝ≥0∞)*ENNReal.ofReal (jacobi.Parameter.youngLower (b/2)))/
        ENNReal.ofReal (standardEnergy (b/2)/4) := by
    rw [show (1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) by norm_num [ENNReal.ofReal_div_of_pos],
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2),
      ← ENNReal.ofReal_div_of_pos (div_pos hC (by norm_num))]
    congr 1
    unfold nesterovYoungRatio
    field_simp
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hmul bot_le

/-- The complete optimal-ratio sandwich. Its lower bound retains the
three homogeneous calibrations; its upper bound uses actual flowed block
competitors and the exact positive Nesterov denominator.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_ratio_sandwich {b : ℝ} (hb : -1<b) :
    ((1/2:ℝ≥0∞)*homogeneousLowerConstant
      (jacobi.Bessel.edgeSpectrum (b/2) (by linarith)))/ENNReal.ofReal (standardEnergy (b/2)/4)≤
        liminf (nesterovClosedRatio b hb) atTop ∧
    liminf (nesterovClosedRatio b hb) atTop≤limsup (nesterovBlockRatio b hb) atTop ∧
    limsup (nesterovBlockRatio b hb) atTop≤
      ENNReal.ofReal (2-12*(b-1)^2/(25*(b+5)^2*(2*b+5)^2*(3*b+5)^2)) := by
  have ha : -(1/2:ℝ)<b/2 := by linarith
  have hC : 0<standardEnergy (b/2)/4 := div_pos (standardEnergy_pos ha) (by norm_num)
  refine ⟨endpoint_ratio_lower _ _ (nesterovEndpointValue_limit hb) (nesterov_all_three_term_lower hb),?_,?_⟩
  · have h := liminf_le_liminf (f := atTop) (Eventually.of_forall (fun n =>
      mul_le_mul_of_nonneg_right (nesterov_closed_le_block (b/2) (by linarith) n)
        (show (0:ℝ≥0∞)≤(ENNReal.ofReal (nesterovEndpointValue b n))⁻¹ from bot_le)))
    exact h.trans liminf_le_limsup
  · have h := endpoint_ratio_upper (nesterovBlockMinimum (b/2) (by linarith))
      (nesterovFlowMajorant (b/2) ha) (nesterovEndpointValue b)
      (nesterovFlowMajorant_limit ha) (nesterovEndpointValue_limit hb) hC (nesterovBlockMajorant ha)
    exact h.trans (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (descentTime_taylor_bound ha) (by norm_num)) hC.le).trans_eq
        (descent_ratio_identity hb)))

/-- The improved block ratio is strictly less than two at every
nonsymmetric parameter. Strictness is exact, not decimal certification.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_block_ratio_lt_two {b : ℝ} (hb : -1<b) (hne : b≠1) :
    limsup (nesterovBlockRatio b hb) atTop<2 := by
  have hg : 0<12*(b-1)^2/(25*(b+5)^2*(2*b+5)^2*(3*b+5)^2) := by
    have hn : b-1≠0 := sub_ne_zero.mpr hne
    have h1 : 0<b+5 := by linarith
    have h2 : 0<2*b+5 := by linarith
    have h3 : 0<3*b+5 := by linarith
    positivity
  exact (nesterov_ratio_sandwich hb).2.2.trans_lt
    (by exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<2)).mpr (by linarith))


/-- The original lower-limiting finite-fibre optimum satisfies the
strict standard-flow improvement at every nonsymmetric admissible order.
Article: jacobi, Corollary 5.7.
-/
theorem jacobiOptimalEnergy_standard_descent {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b)
    (hne : a≠1/2) :
    jacobi.Comparison.jacobiOptimalEnergy a b (by linarith) hb≤
      ENNReal.ofReal (standardEnergy a-descentGap a) ∧
      ENNReal.ofReal (standardEnergy a-descentGap a)<ENNReal.ofReal (standardEnergy a) := by
  have hlim : jacobi.Comparison.jacobiOptimalEnergy a b (by linarith) hb≤
      limsup (fun n : ℕ => fibreEnergyInfimum (jacobi.Jacobi.nodes a b (by linarith) hb (n+1))) atTop :=
    liminf_le_limsup
  refine ⟨hlim.trans (standard_fibre_descent ha hb),?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (standardEnergy_pos ha)).mpr (descentEnergy_lt ha hne)

/-- At the symmetric parameter the whole block class has the same
sharp endpoint constant as the full closed class.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_block_sharp_limit :
    Tendsto (nesterovBlockMinimum (1/2) (by norm_num)) atTop (𝓝 (ENNReal.ofReal (1/15))) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have h := liminf_le_liminf (f := atTop)
      (Eventually.of_forall (nesterov_closed_le_block (1/2) (by norm_num)))
    rwa [nesterov_closed_sharp_limit.liminf_eq] at h
  · have h := nesterov_block_descent (a := (1/2:ℝ)) (by norm_num)
    norm_num [standardEnergy,descentGap] at h ⊢
    exact h
  · exact isBoundedUnder_of ⟨⊤,fun _ => le_top⟩
  · exact isBoundedUnder_of ⟨⊥,fun _ => bot_le⟩

/-- At b=1 the full and block optimal squared endpoint ratios both
converge to two, with their common denominator the actual original method.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_symmetric_ratios :
    Tendsto (nesterovClosedRatio 1 (by norm_num)) atTop (𝓝 2) ∧
      Tendsto (nesterovBlockRatio 1 (by norm_num)) atTop (𝓝 2) := by
  have hD : Tendsto (fun n => ENNReal.ofReal (nesterovEndpointValue 1 n)) atTop
      (𝓝 (ENNReal.ofReal (1/30))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (nesterovEndpointValue_limit (b := 1) (by norm_num))
    norm_num only [standardEnergy] at h
    exact h
  have he : ENNReal.ofReal (1/15)/ENNReal.ofReal (1/30)=(2:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<1/30)]
    norm_num
  constructor
  · unfold nesterovClosedRatio
    have h := ENNReal.Tendsto.div nesterov_closed_sharp_limit
      (Or.inr (by norm_num : ENNReal.ofReal (1/30)≠0)) hD (Or.inl ENNReal.ofReal_ne_top)
    rw [he] at h
    exact h
  · unfold nesterovBlockRatio
    have h := ENNReal.Tendsto.div nesterov_block_sharp_limit
      (Or.inr (by norm_num : ENNReal.ofReal (1/30)≠0)) hD (Or.inl ENNReal.ofReal_ne_top)
    rw [he] at h
    exact h

end
end jacobi.Applications
