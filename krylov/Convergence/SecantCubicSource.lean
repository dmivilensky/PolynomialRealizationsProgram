import krylov.Convergence.SecantThirdVariation

/-!
Article: main_krylov, thm:ss1F, the sharp newer-secant half coefficient.
Use: estimate genuine observed vector secants with the original T3 budget
and only a quadratic L3 remainder. Source: true Riesz derivative fields,
the actual segment midpoint expansion and Banach's spectral identity.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions krylov.Tensor chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- A genuine averaged Hessian has the exact half-weight endpoint
spectral cubic budget and a quadratic Lipschitz-third remainder. -/
theorem averaged_hessian_cubic_endpoint_bound
    (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a b : E) (ha : a∈S) (hb : b∈S) {R : ℝ} (hR : 0≤R)
    (har : ‖a‖≤R) (hbr : ‖b‖≤R) :
    ‖averagedDerivative H a (b-a)-H 0‖≤B/2*(‖a‖+‖b‖)+(L:ℝ)*R^2 := by
  let D := fun z=>canonicalVariation (T z)
  have hD z (hz : z∈S) : HasFDerivAt H (D z) z :=
    hessian_hasFDerivAt_of_scalar_third H (T z) z (hT z hz)
  have hDL := canonicalVariation_lipschitz_of_spectral T S L hLip
  have hp t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈S :=
    hS.add_smul_mem ha (by simpa only [add_sub_cancel] using hb) ht
  have hr t (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖≤R :=
    segment_norm_le_endpoints a b R har hbr t ht
  have hm := averagedHessian_midpoint_quadratic H D S hS h₀ hD hDL a (b-a) R hR
    (fun t ht=>⟨hp t ht,hr t ht⟩)
  let m := a+(1/2:ℝ) • (b-a)
  have hmid : ‖m‖≤(‖a‖+‖b‖)/2 := by
    have he : m=(1/2:ℝ) • a+(1/2:ℝ) • b := by dsimp only [m]; module
    rw [he]
    have hh := norm_add_le ((1/2:ℝ) • a) ((1/2:ℝ) • b)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hh
    exact hh.trans_eq (by ring)
  have hd : ‖D 0 m‖≤B*‖m‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg _))
    intro v
    exact canonicalVariation_action_bound (T 0) hB (cubic_diagonal_bound (T 0) B hbudget) m v
  have hA : ‖averagedDerivative H a (b-a)-H 0‖≤B/2*(‖a‖+‖b‖)+(L:ℝ)*R^2 := by
    have he : averagedDerivative H a (b-a)-H 0=
        (averagedDerivative H a (b-a)-H 0-D 0 m)+D 0 m := by abel
    rw [he]
    have ht := mul_le_mul_of_nonneg_left hmid hB
    exact (norm_add_le _ _).trans ((add_le_add hm (hd.trans ht)).trans_eq (by ring))
  exact hA

/-- The actual current Hessian minus the genuine radial averaged Hessian
has the printed T3/2 term; only the Lipschitz-third remainder is coarsened. -/
theorem hessian_minus_radial_cubic_bound
    (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (x : E) (hx : x∈S) :
    ‖H x-averagedDerivative H 0 x‖≤B/2*‖x‖+2*(L:ℝ)*‖x‖^2 := by
  let D := fun z=>canonicalVariation (T z)
  have hD z (hz : z∈S) : HasFDerivAt H (D z) z :=
    hessian_hasFDerivAt_of_scalar_third H (T z) z (hT z hz)
  have hDL := canonicalVariation_lipschitz_of_spectral T S L hLip
  have hp t (ht : t∈Icc (0:ℝ) 1) : (0:E)+t • x∈S :=
    hS.add_smul_mem h₀ (by simpa only [zero_add] using hx) ht
  have hm := averagedHessian_midpoint_quadratic H D S hS h₀ hD hDL 0 x ‖x‖ (norm_nonneg x)
    (fun t ht=>⟨hp t ht,by
      rw [zero_add,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg x) ht.2⟩)
  have ht := genuine_first_order_quadratic H D S hS h₀ hD hDL x hx
  have hd : ‖D 0 ((1/2:ℝ) • x)‖≤B/2*‖x‖ := by
    have hh := (D 0).le_opNorm ((1/2:ℝ) • x)
    have hn := (canonicalVariation_norm_le_iff_spectral (T 0) hB).mpr hbudget
    have he := hh.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    calc
      _ ≤ B*‖(1/2:ℝ) • x‖ := he
      _ = B/2*‖x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
        ring
  have he : H x-averagedDerivative H 0 x=
      (H x-H 0-D 0 x)-(averagedDerivative H 0 x-H 0-D 0 ((1/2:ℝ) • x))+
        D 0 ((1/2:ℝ) • x) := by
    rw [map_smul]
    module
  simp only [zero_add] at hm
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans (add_le_add ht hm)) hd).trans_eq (by ring))

/-- A true observed secant has exactly the half-weight endpoint T3 term;
the genuinely Lipschitz third derivative contributes only quadratically. -/
theorem secant_image_cubic_endpoint_bound
    (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a b : E) (ha : a∈S) (hb : b∈S) {R : ℝ} (hR : 0≤R)
    (har : ‖a‖≤R) (hbr : ‖b‖≤R) :
    ‖G b-G a-(b-a)‖≤(B/2*(‖a‖+‖b‖)+(L:ℝ)*R^2)*‖b-a‖ := by
  let D := fun z=>canonicalVariation (T z)
  have hD z (hz : z∈S) : HasFDerivAt H (D z) z :=
    hessian_hasFDerivAt_of_scalar_third H (T z) z (hT z hz)
  have hDL := canonicalVariation_lipschitz_of_spectral T S L hLip
  have hp t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈S :=
    hS.add_smul_mem ha (by simpa only [add_sub_cancel] using hb) ht
  have hr t (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖≤R :=
    segment_norm_le_endpoints a b R har hbr t ht
  have hm := averagedHessian_midpoint_quadratic H D S hS h₀ hD hDL a (b-a) R hR
    (fun t ht=>⟨hp t ht,hr t ht⟩)
  let m := a+(1/2:ℝ) • (b-a)
  have hmid : ‖m‖≤(‖a‖+‖b‖)/2 := by
    have he : m=(1/2:ℝ) • a+(1/2:ℝ) • b := by dsimp only [m]; module
    rw [he]
    have hh := norm_add_le ((1/2:ℝ) • a) ((1/2:ℝ) • b)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hh
    exact hh.trans_eq (by ring)
  have hd : ‖D 0 m‖≤B*‖m‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg _))
    intro v
    exact canonicalVariation_action_bound (T 0) hB (cubic_diagonal_bound (T 0) B hbudget) m v
  have hA : ‖averagedDerivative H a (b-a)-H 0‖≤B/2*(‖a‖+‖b‖)+(L:ℝ)*R^2 := by
    have he : averagedDerivative H a (b-a)-H 0=
        (averagedDerivative H a (b-a)-H 0-D 0 m)+D 0 m := by abel
    rw [he]
    have ht := mul_le_mul_of_nonneg_left hmid hB
    exact (norm_add_le _ _).trans ((add_le_add hm (hd.trans ht)).trans_eq (by ring))
  have hcont : ContinuousOn H S := fun z hz=>(hD z hz).continuousAt.continuousWithinAt
  have hc := hcont.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
  have he := averagedDerivative_apply G H a (b-a) hc (fun t ht=>hG _ (hp t ht))
  simp only [add_sub_cancel] at he
  have hid : G b-G a-(b-a)=(averagedDerivative H a (b-a)-H 0) (b-a) := by
    rw [sub_apply,he,hH₀,ContinuousLinearMap.id_apply]
  rw [hid]
  exact ((averagedDerivative H a (b-a)-H 0).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

end
end krylov.Convergence
