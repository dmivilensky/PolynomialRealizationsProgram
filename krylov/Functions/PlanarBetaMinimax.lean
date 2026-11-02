import krylov.Functions.PlanarRFCFBetaModel
import krylov.Functions.PlanarSharpShrink
import krylov.Functions.BudgetedPlaneCentre
import krylov.Functions.PlanarBetaCentre

/-!
Article: main_krylov, thm:Fplanar, independent-base value-information minimax.
Use: retain the complete independent base interval in the actual planar
scalar risk and include every unrestricted observation-only output policy.
The lower bound uses an attained true information chord at beta zero;
the matching upper bound is supplied by the endpoint-only budgeted centre.
Source: actual scalar gradients and the proved attained binary information
radius. No boundedness or regularity of competing outputs is assumed.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped ENNReal

/-- Actual planar value-information worst risk over the entire compatible
tensor ball and the independent unknown base interval. Article: thm:Fplanar. -/
def planeBetaPolicyWorst (B r p L : ℝ) (policy : Observation → Plane) : ℝ≥0∞ :=
  ⨆ t : {t : krylov.Tensor.BinaryCubic // t.InBall},
    ⨆ β : {β : ℝ // |β|≤L*p},
      ENNReal.ofReal ‖gradient (planeBetaCubicObjective p r β.val (scaleBinaryCubic B t.val))
        (policy (observe r (scaleBinaryCubic B t.val)))‖

/-- The actual independent-base planar minimax, allowing unrestricted
observation-only decisions, including unbounded ones. Article: thm:Fplanar. -/
def planeBetaPolicyMinimax (B r p L : ℝ) : ℝ≥0∞ :=
  ⨅ policy : Observation → Plane, planeBetaPolicyWorst B r p L policy

set_option maxHeartbeats 800000 in
/-- One attained true chord supplies the sharp all-policy lower bound
for the entire independent-base source class. Its fixed fourth-order loss
is uniform in the competing policy and independent base interval.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaPolicyWorst_lower (B r : ℝ) (hB : 0<B) (hr : 0<r) :
    ∃ C : ℝ, 0<C ∧ ∀ p L : ℝ, 0<p → B*p≤1 → 0≤L →
      ∀ policy : Observation → Plane,
      ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-C*p^4)≤
        planeBetaPolicyWorst B r p L policy := by
  obtain ⟨t,u,hch,hatt⟩ := exists_chord_attaining_fibreMinimax r
  have hd : u.t2-t.t2≠0 := by
    intro he
    have hv := binaryFibreMinimax_pos r
    rw [←hatt] at hv
    have he' : t.t2-u.t2=0 := by linarith only [he]
    simp only [chordValue,he',abs_zero,mul_zero,zero_div] at hv
    exact (lt_irrefl 0) hv
  obtain ⟨C,hC,hlower⟩ := planeCubic_scaled_all_output_lower r t u (chord_observations hch) hd hr.ne'
  refine ⟨C*B^3,mul_pos hC (pow_pos hB _),?_⟩
  intro p L hp hp₁ hL policy
  have hobs := scaleBinaryCubic_observe_equal r B t u (chord_observations hch)
  have hbeta : |(0 : ℝ)|≤L*p := by simpa only [abs_zero] using mul_nonneg hL hp.le
  have hb := hlower p B hp hB hp₁ (policy (observe r (scaleBinaryCubic B t)))
  rw [hatt] at hb
  have hcoeff : B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-(C*B^3)*p^4=
      B^2*(r^2/4*fibreMinimax r*Real.sqrt (1+4*r^2))*p^3-C*B^3*p^4 := by ring
  rw [hcoeff]
  apply (ENNReal.ofReal_le_ofReal hb).trans
  rw [ENNReal.ofReal_max]
  apply max_le
  · apply le_iSup_of_le ⟨t,hch.1⟩
    apply le_iSup_of_le ⟨0,hbeta⟩
    simp only [planeBetaCubicGradient_actual,zero_mul,zero_smul,add_zero]
    exact le_rfl
  · apply le_iSup_of_le ⟨u,hch.2.1⟩
    apply le_iSup_of_le ⟨0,hbeta⟩
    simp only [planeBetaCubicGradient_actual,zero_mul,zero_smul,add_zero,←hobs]
    exact le_rfl

/-- The actual centre controls the supremum over every independent beta,
with the same leading constant as the information lower bound.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaPolicyWorst_centre_upper (B r L : ℝ) (hB : 0<B) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      planeBetaPolicyWorst B r p L (budgetedPlaneCentreOutput B r p)≤
        ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4) := by
  obtain ⟨C,hC,hupper⟩ := budgetedPlaneCentreOutput_beta_gradient_upper B r L hB hL
  refine ⟨C,hC,?_⟩
  intro p hp hp₁
  apply iSup_le
  intro t
  apply iSup_le
  intro β
  exact ENNReal.ofReal_le_ofReal (hupper p hp hp₁ β.val β.property t.val t.property)

/-- The literal independent-base infimum of actual function suprema has
the exact attained information coefficient, with uniform O(p^4) losses.
The admissible endpoint-only centre supplies the upper comparison.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaPolicyMinimax_bounds (B r L : ℝ) (hB : 0<B) (hr : 0<r) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-C*p^4)≤
        planeBetaPolicyMinimax B r p L ∧
      planeBetaPolicyMinimax B r p L≤
        ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4) := by
  obtain ⟨Cl,hCl,hlower⟩ := planeBetaPolicyWorst_lower B r hB hr
  obtain ⟨Cu,hCu,hupper⟩ := planeBetaPolicyWorst_centre_upper B r L hB hL
  refine ⟨Cl+Cu,by positivity,?_⟩
  intro p hp hp₁
  constructor
  · apply le_iInf
    intro policy
    apply (ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (mul_le_mul_of_nonneg_right (by linarith only [hCu] : Cl≤Cl+Cu) (pow_nonneg hp.le 4)) _)).trans
    exact hlower p L hp hp₁ hL policy
  · apply (iInf_le (fun policy : Observation → Plane=>planeBetaPolicyWorst B r p L policy)
      (budgetedPlaneCentreOutput B r p)).trans
    exact (hupper p hp hp₁).trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by linarith only [hCl] : Cu≤Cl+Cu) (pow_nonneg hp.le 4))))

end
end krylov.Functions
