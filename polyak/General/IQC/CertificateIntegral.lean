import polyak.General.IQC.CertificateSymbol
import polyak.General.IQC.HomotopyFourier

/-! Article: lem:iqc(a). The quadratic source expression on L² is
the literal integral of its pointwise two-channel expression. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy MeasureTheory
open scoped ENNReal

variable {Ω E H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem integral_L2_norm_sq (x : Lp E 2 μ) : (∫ ω,‖x ω‖^2 ∂μ)=‖x‖^2 := by
  calc
    _=inner ℝ x x := by rw [L2.inner_def]; simp only [real_inner_self_eq_norm_sq]
    _=‖x‖^2 := real_inner_self_eq_norm_sq _
theorem integrable_L2_norm_sq (x : Lp E 2 μ) : Integrable (fun ω => ‖x ω‖^2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜:=ℝ) x x

theorem pairQuadratic_integrable (δ : ℝ) (x y σ τ : Lp E 2 μ) :
    Integrable (fun ω => pairQuadratic δ (x ω) (y ω) (σ ω) (τ ω)) μ := by
  have hd : Integrable (fun ω => ‖y ω-x ω‖^2) μ :=
    (integrable_L2_norm_sq (y-x)).congr (by
      filter_upwards [Lp.coeFn_sub y x] with ω hω
      rw [hω]; rfl)
  have hds : Integrable (fun ω => ‖τ ω-σ ω‖^2) μ :=
    (integrable_L2_norm_sq (τ-σ)).congr (by
      filter_upwards [Lp.coeFn_sub τ σ] with ω hω
      rw [hω]; rfl)
  have hi : Integrable (fun ω => inner ℝ (σ ω+τ ω) (y ω-x ω)) μ :=
    (L2.integrable_inner (𝕜:=ℝ) (σ+τ) (y-x)).congr (by
      filter_upwards [Lp.coeFn_add σ τ,Lp.coeFn_sub y x] with ω ha hs
      rw [ha,hs]; rfl)
  exact ((hd.sub hds).const_mul (1/4)).sub (hi.const_mul (δ/2))

theorem pairQuadratic_integral (δ : ℝ) (x y σ τ : Lp E 2 μ) :
    pairQuadratic δ x y σ τ=(∫ ω,pairQuadratic δ (x ω) (y ω) (σ ω) (τ ω) ∂μ) := by
  have hd : Integrable (fun ω => ‖y ω-x ω‖^2) μ :=
    (integrable_L2_norm_sq (y-x)).congr (by
      filter_upwards [Lp.coeFn_sub y x] with ω hω
      rw [hω]; rfl)
  have hds : Integrable (fun ω => ‖τ ω-σ ω‖^2) μ :=
    (integrable_L2_norm_sq (τ-σ)).congr (by
      filter_upwards [Lp.coeFn_sub τ σ] with ω hω
      rw [hω]; rfl)
  have hi : Integrable (fun ω => inner ℝ (σ ω+τ ω) (y ω-x ω)) μ :=
    (L2.integrable_inner (𝕜:=ℝ) (σ+τ) (y-x)).congr (by
      filter_upwards [Lp.coeFn_add σ τ,Lp.coeFn_sub y x] with ω ha hs
      rw [ha,hs]; rfl)
  unfold pairQuadratic
  have hlin := integral_sub ((hd.sub hds).const_mul (1/4:ℝ)) (hi.const_mul (δ/2))
  simp only [Pi.sub_apply] at hlin
  rw [hlin,integral_const_mul,integral_const_mul]
  have hdiff := integral_sub hd hds
  rw [hdiff]
  have hd' : (∫ ω,‖y ω-x ω‖^2 ∂μ)=‖y-x‖^2 := by
    rw [← integral_L2_norm_sq (y-x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub y x] with ω hω
    rw [hω]; rfl
  have hds' : (∫ ω,‖τ ω-σ ω‖^2 ∂μ)=‖τ-σ‖^2 := by
    rw [← integral_L2_norm_sq (τ-σ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub τ σ] with ω hω
    rw [hω]; rfl
  have hi' : (∫ ω,inner ℝ (σ ω+τ ω) (y ω-x ω) ∂μ)=inner ℝ (σ+τ) (y-x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add σ τ,Lp.coeFn_sub y x] with ω ha hs
    rw [ha,hs]; rfl
  rw [hd',hds',hi']

theorem starQuadratic_integrable (δ : ℝ) (x σ : Lp E 2 μ) :
    Integrable (fun ω => starQuadratic δ (x ω) (σ ω)) μ :=
  (((integrable_L2_norm_sq x).sub (integrable_L2_norm_sq σ)).const_mul (1/4)).sub
    ((L2.integrable_inner (𝕜:=ℝ) σ x).const_mul (δ/2))
theorem starQuadratic_integral (δ : ℝ) (x σ : Lp E 2 μ) :
    starQuadratic δ x σ=(∫ ω,starQuadratic δ (x ω) (σ ω) ∂μ) := by
  unfold starQuadratic
  have hlin := integral_sub (((integrable_L2_norm_sq x).sub (integrable_L2_norm_sq σ)).const_mul (1/4:ℝ))
    ((L2.integrable_inner (𝕜:=ℝ) σ x).const_mul (δ/2))
  simp only [Pi.sub_apply] at hlin
  rw [hlin,integral_const_mul,integral_const_mul]
  have hdiff := integral_sub (integrable_L2_norm_sq x) (integrable_L2_norm_sq σ)
  rw [hdiff,integral_L2_norm_sq,integral_L2_norm_sq,← L2.inner_def]

theorem pairQuadratic_unitary (U : H≃ₗᵢ[ℝ]Lp E 2 μ) (δ : ℝ) (x y σ τ : H) :
    pairQuadratic δ (U x) (U y) (U σ) (U τ)=pairQuadratic δ x y σ τ := by
  simp only [pairQuadratic,← U.map_sub,← U.map_add,U.norm_map,U.inner_map_map]
theorem starQuadratic_unitary (U : H≃ₗᵢ[ℝ]Lp E 2 μ) (δ : ℝ) (x σ : H) :
    starQuadratic δ (U x) (U σ)=starQuadratic δ x σ := by
  simp only [starQuadratic,U.norm_map,U.inner_map_map]

end polyak.General.IQC
