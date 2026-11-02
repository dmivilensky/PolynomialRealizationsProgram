import krylov.Asymptotics.SharpLowerLimit
import krylov.Asymptotics.UpperLimitAlgebra

/-!
Article: main_krylov, thm:limit, complete sharp discrete-to-continuum limit.
Use: match the actual finite/infinite all-measure upper bounds with the
genuine finite recovery designs. All positive source exponents, arbitrary
diverging condition-number families, and simultaneous growing finite
cycles are included. The source n−1 indexing is explicit.
Source: the constructed stage-9 optimizer and the proved actual finite
Stieltjes, sharp step-cancellation, Gershgorin and recovery theorems.
-/

/-!
Article: krylov, Theorem D.9 [thm:limit].

The exact finite-condition upper expression and both sharp infinite/finite-horizon limits use
the same constructed feedback graph and genuine discrete recovery.
The finite-horizon limit explicitly assumes nθ→∞; graphBound is γ below one and 1/2 at γ=1.
Theorem 5.1 [thm:amplification] is the half- and unit-exponent specialization, with the
same infinite-horizon and nθ → ∞ finite-horizon limits.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory
open krylov.Design krylov.ContinuumControl
open scoped Topology
universe u

/-- The actual infinite optimized design criterion has the sharp continuum
limit along every diverging family of physical condition numbers. -/
theorem infinitePowerValue_scaled_tendsto {ι : Type u} {l : Filter ι}
    {I : ι → chebyshev1.SpectralInterval} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop)
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (hnear : ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ)) :
    Tendsto (fun i ↦ designSpacing (I i) * infinitePowerValue (I i) γ) l
      (𝓝 (feedbackValue γ σ 1)) := by
  have hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hκ
  have hupper := finiteDesignUpper_scaled_tendsto hκ hγ hB σ
  refine tendsto_order.2 ⟨fun b hb ↦ eventually_lower_sharp_infinite hγ hnear hR hb, ?_⟩
  intro b hb
  filter_upwards [hupper.eventually (Iio_mem_nhds hb)] with i hi
  exact (mul_le_mul_of_nonneg_left
    (infinitePowerValue_sharp_upper (I i) hγ hγ₁ hB hgraph hlog)
    (designSpacing_pos (I i)).le).trans_lt hi

/-- The same sharp limit holds for every genuine finite degree budget
whose source type-time budget M theta diverges. -/
theorem optimalValue_scaled_tendsto {ι : Type u} {l : Filter ι}
    {I : ι → chebyshev1.SpectralInterval} {M : ι → ℕ} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop)
    (hM : Tendsto (fun i ↦ (M i : ℝ) * designSpacing (I i)) l atTop)
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (hnear : ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ)) :
    Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) γ) l
      (𝓝 (feedbackValue γ σ 1)) := by
  have hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hκ
  have hupper := finiteDesignUpper_scaled_tendsto hκ hγ hB σ
  refine tendsto_order.2 ⟨fun b hb ↦ eventually_lower_sharp_finite hγ hnear hR hM hb, ?_⟩
  intro b hb
  filter_upwards [hupper.eventually (Iio_mem_nhds hb)] with i hi
  exact (mul_le_mul_of_nonneg_left
    (optimalValue_sharp_upper (I i) (M i) hγ hγ₁ hB hgraph hlog)
    (designSpacing_pos (I i)).le).trans_lt hi

/-- The article's finite n-atom / n−1-degree criterion has exactly the
same limit under its original simultaneous condition n theta→infinity. -/
theorem preterminal_optimalValue_scaled_tendsto {ι : Type u} {l : Filter ι}
    {I : ι → chebyshev1.SpectralInterval} {n : ι → ℕ} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun i ↦ (I i).kappa) l atTop)
    (hn : Tendsto (fun i ↦ (n i : ℝ) * designSpacing (I i)) l atTop)
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
    (hnear : ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ)) :
    Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (n i - 1) (fun _ ↦ 1) γ) l
      (𝓝 (feedbackValue γ σ 1)) :=
  optimalValue_scaled_tendsto hκ
    (preterminal_mesh_diverges (designSpacing_tendsto_zero hκ)
      (Eventually.of_forall (fun i ↦ designSpacing_pos (I i))) hn)
    hγ hγ₁ hB hgraph hlog hnear

/-- All sharp upper and lower source conclusions hold for one and the
same actually constructed analytic separating graph, for every 0<γ≤1.
No smooth optimizer, recovery limit or spectral certificate is an input. -/
theorem exists_full_sharp_limit {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ, (∀ r ≥ 1, AnalyticAt ℝ σ r) ∧
      (∀ r ≥ 1, FeedbackGraphAt γ σ r) ∧
      (∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ graphBound γ) ∧
      (∀ I : chebyshev1.SpectralInterval, ∀ M : ℕ,
        optimalValue I M (fun _ ↦ 1) γ ≤ finiteDesignUpper I γ (graphBound γ) σ) ∧
      (∀ I : chebyshev1.SpectralInterval,
        infinitePowerValue I γ ≤ finiteDesignUpper I γ (graphBound γ) σ) ∧
      (∀ {ι : Type u} {l : Filter ι} {I : ι → chebyshev1.SpectralInterval},
        Tendsto (fun i ↦ (I i).kappa) l atTop →
        Tendsto (fun i ↦ designSpacing (I i) * infinitePowerValue (I i) γ) l
          (𝓝 (feedbackValue γ σ 1))) ∧
      ∀ {ι : Type u} {l : Filter ι} {I : ι → chebyshev1.SpectralInterval} {n : ι → ℕ},
        Tendsto (fun i ↦ (I i).kappa) l atTop →
        Tendsto (fun i ↦ (n i : ℝ) * designSpacing (I i)) l atTop →
        Tendsto (fun i ↦ designSpacing (I i) * optimalValue (I i) (n i - 1) (fun _ ↦ 1) γ) l
          (𝓝 (feedbackValue γ σ 1)) := by
  obtain ⟨σ, ha, hg, hl, hn⟩ := exists_sharp_recovery_graph hγ hγ₁
  have hB : 0 ≤ graphBound γ := by unfold graphBound; split_ifs <;> positivity
  refine ⟨σ, ha, hg, hl, fun I M ↦ optimalValue_sharp_upper I M hγ hγ₁ hB hg hl,
    fun I ↦ infinitePowerValue_sharp_upper I hγ hγ₁ hB hg hl, ?_, ?_⟩
  · intro ι l I hκ
    exact infinitePowerValue_scaled_tendsto hκ hγ hγ₁ hB hg hl hn
  · intro ι l I n hκ hcycle
    exact preterminal_optimalValue_scaled_tendsto hκ hcycle hγ hγ₁ hB hg hl hn

end
end krylov.Asymptotics
