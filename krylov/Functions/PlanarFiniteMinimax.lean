import krylov.Functions.PlanarPolicyTaylor
import krylov.Functions.PlanarAttainedChord

/-!
Article: main_krylov, thm:Fplanar, complete finite-scale function minimax.
Use: take the infimum over every unrestricted observation-only output and
the supremum over all genuine admissible scalar cubics. Both sharp leading
bounds have fixed uniform fourth-order errors; one concrete centre policy
attains the upper bound. Source: the attained true chord and exact cubic
query/output polynomial identities.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped ENNReal

/-- The actual scalar-function minimax over all observation-only outputs,
including unrestricted and unbounded policies. Article: main_krylov, thm:Fplanar. -/
def planeCubicPolicyMinimax (r p : ℝ) : ℝ≥0∞ :=
  ⨅ policy : Observation → Plane, planeCubicPolicyWorst r p policy

/-- The true full information radius yields a fixed fourth-order actual
function lower remainder, simultaneously for every unrestricted policy.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planeCubicPolicyWorst_lower_quartic (r : ℝ) (hr : 0<r) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ policy : Observation → Plane,
      ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-C*p^4)≤
        planeCubicPolicyWorst r p policy := by
  by_cases hzero : fibreMinimax r≤0
  · refine ⟨1,zero_lt_one,?_⟩
    intro p hp _ policy
    have hh : r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-1*p^4≤0 := by
      have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤r^2/4*Real.sqrt (1+4*r^2)) hzero
      have hn' := mul_nonpos_of_nonpos_of_nonneg hn (pow_nonneg hp.le 3)
      linarith only [hn',pow_nonneg hp.le 4]
    rw [ENNReal.ofReal_of_nonpos hh]
    exact bot_le
  · have hMF : 0<fibreMinimax r := lt_of_not_ge hzero
    obtain ⟨t,u,hchord,hvalue⟩ := exists_chord_attaining_fibreMinimax r
    have hd : u.t2-t.t2≠0 := by
      intro he
      have hh : t.t2-u.t2=0 := by linarith only [he]
      have hv := hvalue
      simp only [chordValue,hh,abs_zero,mul_zero,zero_div] at hv
      linarith only [hv,hMF]
    have hobs := chord_observations hchord
    obtain ⟨C,hC,hlower⟩ := planeCubic_all_output_chord_lower r t u hobs hd hr.ne'
    refine ⟨C,hC,?_⟩
    intro p hp hp₁ policy
    have hh := hlower p hp hp₁ (policy (observe r t))
    rw [hvalue] at hh
    have heq : r^2/4*fibreMinimax r*Real.sqrt (1+4*r^2)=r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r := by ring
    rw [heq] at hh
    apply (ENNReal.ofReal_le_ofReal hh).trans
    rw [ENNReal.ofReal_max]
    apply max_le
    · exact le_iSup_of_le ⟨t,hchord.1⟩ le_rfl
    · have hb := le_iSup_of_le (i:=⟨u,hchord.2.1⟩)
        (f:=fun t : {t : krylov.Tensor.BinaryCubic // t.InBall}=>
          ENNReal.ofReal ‖gradient (planeCubicObjective p r t.val) (policy (observe r t.val))‖) le_rfl
      simpa only [←hobs] using! hb

/-- The explicit actual finite-scale centre policy has the sharp leading
worst-gradient coefficient with a fixed fourth-order error.
Article: main_krylov, thm:Fplanar. -/
theorem planeCubicPolicyWorst_centre_upper (r : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 →
      planeCubicPolicyWorst r p (planeCentreOutput r p)≤
        ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3+C*p^4) := by
  obtain ⟨C,hC,hupper⟩ := planeCentreOutput_gradient_upper r
  refine ⟨C,hC,?_⟩
  intro p hp hp₁
  apply iSup_le
  intro t
  exact ENNReal.ofReal_le_ofReal (hupper p hp hp₁ t.val t.property)

/-- The complete original scalar cubic minimax has the exact leading value
(r²/4) sqrt(1+4r²) M_F(r) p³ and fixed two-sided O(p⁴) errors.
Competitors include every unrestricted observation-only output policy.
The explicit true-fibre centre realizes the upper bound.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planeCubicPolicyMinimax_bounds (r : ℝ) (hr : 0<r) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 →
      ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-C*p^4)≤
        planeCubicPolicyMinimax r p ∧
      planeCubicPolicyMinimax r p≤
        ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3+C*p^4) := by
  obtain ⟨Cl,hCl,hlower⟩ := planeCubicPolicyWorst_lower_quartic r hr
  obtain ⟨Cu,hCu,hupper⟩ := planeCubicPolicyWorst_centre_upper r
  refine ⟨Cl+Cu,by positivity,?_⟩
  intro p hp hp₁
  constructor
  · apply le_iInf
    intro policy
    apply (ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (mul_le_mul_of_nonneg_right (by linarith only [hCu] : Cl≤Cl+Cu) (pow_nonneg hp.le 4)) _)).trans
    exact hlower p hp hp₁ policy
  · apply (iInf_le (fun policy : Observation → Plane=>planeCubicPolicyWorst r p policy)
      (planeCentreOutput r p)).trans
    exact (hupper p hp hp₁).trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by linarith only [hCl] : Cu≤Cl+Cu) (pow_nonneg hp.le 4))))

end
end krylov.Functions
