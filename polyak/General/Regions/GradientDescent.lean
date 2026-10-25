import polyak.General.Regions.QuadraticLower
import polyak.General.Regions.Explicit
import polyak.Dynamics.Original

/-! Article: Corollary D(b). The exact original nonlinear rate of gradient
descent is proved by a pointwise normalized-gradient contraction, uniformly
in functions, dimensions, and horizons. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Filter Set
open scoped Topology

private theorem normalizedState_norm_le_zero_beta {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (σ : E→E)
    (hσ : ∀ x,‖σ x‖≤‖x‖) (A B : ℝ) (x₀ : E) (n : ℕ) :
    ‖(normalizedState σ A B 0 x₀ n).1‖≤(|A|+|B|)^n*‖x₀‖ := by
  induction n with
  | zero => simp [normalizedState]
  | succ n ih =>
    simp only [normalizedState,normalizedStep,zero_smul,sub_zero]
    calc
      ‖A • (normalizedState σ A B 0 x₀ n).1+B • σ (normalizedState σ A B 0 x₀ n).1‖
          ≤ ‖A • (normalizedState σ A B 0 x₀ n).1‖+
            ‖B • σ (normalizedState σ A B 0 x₀ n).1‖ := norm_add_le _ _
      _ ≤ (|A|+|B|)*‖(normalizedState σ A B 0 x₀ n).1‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
        nlinarith [mul_le_mul_of_nonneg_left (hσ (normalizedState σ A B 0 x₀ n).1) (abs_nonneg B)]
      _ ≤ (|A|+|B|)*((|A|+|B|)^n*‖x₀‖) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (|A|+|B|)^(n+1)*‖x₀‖ := by ring

/-- One actual gradient-descent run has the sharp all-horizon contraction. -/
theorem gradientDescent_iterate_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ L α : ℝ} {f : E→ℝ}
    (hf : SmoothStronglyConvex μ L f) (hα : 0≤α)
    (a : E) (hmin : ∀ y,f a≤f y) (x₀ : E) (n : ℕ) :
    ‖iterate (gradient f) α 0 x₀ n-a‖≤
      (max |1-α*μ| |1-α*L|)^n*‖x₀-a‖ := by
  obtain ⟨hψ,hmodel⟩ := original_normalized_run hf a hmin α 0 x₀
  have hg (x : E) : ‖gradient (originalPotential μ L f a) x‖≤‖x‖ := by
    have hh := hψ.grad_lipschitz.norm_sub_le x 0
    simpa only [hψ.gradient_zero,sub_zero,NNReal.coe_one,one_mul] using hh
  have hh := normalizedState_norm_le_zero_beta _ hg
    (normalizedA μ L α 0) (normalizedB μ L α) (x₀-a) n
  have hB : 0≤normalizedB μ L α := by unfold normalizedB; positivity [hf.mu_lt_L]
  rw [abs_of_nonneg hB,normalizedA_abs_add_B_eq hf.mu_lt_L.le hα] at hh
  simp only [add_zero] at hh
  simpa only [← congrArg Prod.fst (hmodel n),iterate] using hh

/-- Taking the true dimension-uniform supremum preserves the sharp bound. -/
theorem gradientDescent_worstAll_le {μ L α : ℝ} (hα : 0≤α) (n : ℕ) :
    worstAll μ L α 0 n≤(max |1-α*μ| |1-α*L|)^n := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl|⟨_,_,f,hf,a,x₀,hmin,hx,rfl⟩
  · positivity
  · exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hx))).mpr
      (gradientDescent_iterate_bound hf hα a hmin x₀ n)

/-- Sharp upper bound for the original limsup rate, rather than the free-state rate. -/
theorem gradientDescent_rate_le {μ L α : ℝ} (hμ : 0<μ) (hL : μ<L) (hα : 0≤α) :
    rate μ L α 0≤max |1-α*μ| |1-α*L| := by
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n =>
    Real.rpow_nonneg (worstAll_nonneg hμ hL hα (by norm_num) n) _))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hR : 0≤max |1-α*μ| |1-α*L| := le_trans (abs_nonneg _) (le_max_left _ _)
  calc
    worstAll μ L α 0 n^((n:ℝ)⁻¹)≤
        ((max |1-α*μ| |1-α*L|)^n)^((n:ℝ)⁻¹) :=
      Real.rpow_le_rpow (worstAll_nonneg hμ hL hα (by norm_num) n)
        (gradientDescent_worstAll_le hα n) (by positivity)
    _ = _ := Real.pow_rpow_inv_natCast hR (by omega)

/-- Corollary D(b), exact actual nonlinear rate in all admissible beta=0 tunings. -/
theorem gradientDescent_rate_eq (q : Tuning) (hb : q.beta=0) :
    rate q.x q.y 1 q.beta=max |1-q.x| |1-q.y| := by
  apply le_antisymm
  · rw [hb]
    simpa only [one_mul] using gradientDescent_rate_le q.x_pos q.x_lt_y (by norm_num : (0:ℝ)≤1)
  · have hroot : rootRadius (1+q.beta-q.x) q.beta=|1-q.x| := by
      simp only [hb,add_zero,rootRadius]
      split_ifs with h
      · have : 1-q.x=0 := by nlinarith [sq_nonneg (1-q.x)]
        simp [this]
      · simp only [mul_zero,sub_zero,Real.sqrt_sq_eq_abs]
        ring
    have hroot' : rootRadius (1+q.beta-q.y) q.beta=|1-q.y| := by
      simp only [hb,add_zero,rootRadius]
      split_ifs with h
      · have : 1-q.y=0 := by nlinarith [sq_nonneg (1-q.y)]
        simp [this]
      · simp only [mul_zero,sub_zero,Real.sqrt_sq_eq_abs]
        ring
    simpa only [Tuning.rhoQ,Tuning.rhoA,Tuning.rhoB,hroot,hroot'] using rhoQ_le_rate q

/-- Gradient descent belongs to the entire lag-one convergence region. -/
theorem gradientDescent_mem_omegaOne (q : Tuning) (hb : q.beta=0) : OmegaOne q :=
  (omegaOne_iff_explicit q).mpr (Or.inl hb)

end
end polyak.General.Regions
