import krylov.Tensor.BinaryFibreRadius
import Mathlib.Basic.ENNReal.Real

/-!
Article: main_krylov, thm:Fplanar, sharp minimax of the genuine leading
binary observation problem.
Use: quantify over every observation-dependent output, including unbounded
policies, and every tensor in the original diagonal-norm ball. The exact
minimax is M_F(r)*norm(v), attained by the explicit observed-fibre centre.
Source: the actual interval endpoints and the already proved two-scenario
half-distance theorem. Extended nonnegative suprema retain arbitrary policies.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open krylov.LinearAlgebra
open scoped ENNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The full worst error of an arbitrary data-only output policy.
Article: main_krylov, thm:Fplanar.
Extended nonnegative suprema also cover policies with unbounded outputs. -/
def policyWorstError (r : ℝ) (v : V) (policy : Observation → V) : ℝ≥0∞ :=
  ⨆ t : {t : BinaryCubic // t.InBall},
    ENNReal.ofReal ‖policy (observe r t.val)+((observe r t.val).P*t.val.t2) • v‖

/-- The actual infimum over every policy using precisely the observed data.
Article: main_krylov, thm:Fplanar, leading planar information problem. -/
def policyMinimax (r : ℝ) (v : V) : ℝ≥0∞ :=
  ⨅ policy : Observation → V, policyWorstError r v policy

/-- The explicit centre policy depends on the observed coefficients alone.
Article: main_krylov, thm:Fplanar. -/
def centrePolicy (r : ℝ) (v : V) : Observation → V := fun O => fibreCentreCorrection r O v

/-- Every arbitrary policy obeys each actual tensor chord's lower radius.
Article: main_krylov, thm:Fplanar, all-policy information lower bound. -/
theorem chord_policy_lower {r : ℝ} {y z : BinaryCubic} (h : Chord r y z)
    (v : V) (policy : Observation → V) :
    ENNReal.ofReal (chordValue r y z*‖v‖)≤policyWorstError r v policy := by
  let P := (observe r y).P
  let u := policy (observe r y)
  have he : (P*y.t2) • v-(P*z.t2) • v=(P*(y.t2-z.t2)) • v := by module
  have hd := two_scenario_distance ((P*y.t2) • v) ((P*z.t2) • v) u
  rw [he,norm_smul,Real.norm_eq_abs,abs_mul] at hd
  have hval : |P| * |y.t2-z.t2| * ‖v‖/2=chordValue r y z*‖v‖ := by
    unfold chordValue
    dsimp only [P,observe]
    ring
  rw [hval] at hd
  have hyl := le_iSup (fun t : {t : BinaryCubic // t.InBall} =>
    ENNReal.ofReal ‖policy (observe r t.val)+((observe r t.val).P*t.val.t2) • v‖) ⟨y,h.1⟩
  have hzl := le_iSup (fun t : {t : BinaryCubic // t.InBall} =>
    ENNReal.ofReal ‖policy (observe r t.val)+((observe r t.val).P*t.val.t2) • v‖) ⟨z,h.2.1⟩
  have hobs := chord_observations h
  rw [← hobs] at hzl
  apply (ENNReal.ofReal_le_ofReal hd).trans
  rw [ENNReal.ofReal_max]
  apply max_le
  · simpa only [u,P,add_comm,policyWorstError] using! hyl
  · simpa only [u,P,add_comm,policyWorstError] using! hzl

/-- Every policy has worst error at least the full actual minimax coefficient.
Article: main_krylov, thm:Fplanar, supremum over all genuine information chords. -/
theorem policyWorstError_lower (r : ℝ) (v : V) (policy : Observation → V) :
    ENNReal.ofReal (fibreMinimax r*‖v‖)≤policyWorstError r v policy := by
  by_cases htop : policyWorstError r v policy=⊤
  · rw [htop]
    exact le_top
  by_cases hv : ‖v‖=0
  · simp only [hv,mul_zero,ENNReal.ofReal_zero,zero_le]
  have hvpos : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hMF : fibreMinimax r≤(policyWorstError r v policy).toReal/‖v‖ := by
    apply csSup_le ⟨0,zero_mem_chordValues r⟩
    rintro a ⟨y,z,h,rfl⟩
    have hp := (ENNReal.ofReal_le_iff_le_toReal htop).mp (chord_policy_lower h v policy)
    exact (le_div_iff₀ hvpos).mpr hp
  apply ENNReal.ofReal_le_of_le_toReal
  exact (le_div_iff₀ hvpos).mp hMF

/-- The explicit centre policy achieves the sharp radius simultaneously on
all actual observed fibres. Article: main_krylov, thm:Fplanar. -/
theorem centrePolicy_upper (r : ℝ) (v : V) :
    policyWorstError r v (centrePolicy r v)≤ENNReal.ofReal (fibreMinimax r*‖v‖) := by
  apply iSup_le
  intro t
  have ht := self_mem_coefficientFibre t.property r
  have hc := fibre_centre_error v ht
  have hm := mul_le_mul_of_nonneg_right
    (fibreProduct_le_minimax r (observe r t.val) ⟨t.val.t2,ht⟩) (norm_nonneg v)
  exact ENNReal.ofReal_le_ofReal (hc.trans hm)

/-- The complete leading planar observation minimax has its exact coefficient,
and the explicit data-only centre policy attains it.
Article: main_krylov, thm:Fplanar.
Proof: all policies satisfy the all-chord lower radius, while one actual
policy attains its opposite bound on the entire genuine tensor ball. -/
theorem policyMinimax_eq (r : ℝ) (v : V) :
    policyMinimax r v=ENNReal.ofReal (fibreMinimax r*‖v‖) := by
  apply le_antisymm
  · exact (iInf_le (fun policy : Observation → V => policyWorstError r v policy)
      (centrePolicy r v)).trans (centrePolicy_upper r v)
  · apply le_iInf
    intro policy
    exact policyWorstError_lower r v policy

/-- The actual centre policy attains the full global minimax.
Article: main_krylov, thm:Fplanar. -/
theorem centrePolicy_optimal (r : ℝ) (v : V) :
    policyWorstError r v (centrePolicy r v)=policyMinimax r v := by
  rw [policyMinimax_eq]
  exact le_antisymm (centrePolicy_upper r v) (policyWorstError_lower r v _)

/-- The true planar direction of the remaining hidden binary coefficient.
Article: main_krylov, thm:Fplanar, N e=(-2r,1). -/
def planarFibreDirection (r : ℝ) : Plane := WithLp.toLp 2 ![-2*r,1]

/-- The actual information direction has the printed norm sqrt(1+4r²).
Article: main_krylov, thm:Fplanar. -/
theorem planarFibreDirection_norm (r : ℝ) : ‖planarFibreDirection r‖=Real.sqrt (1+4*r^2) := by
  have h := plane_norm_sq (planarFibreDirection r)
  have hsq : ‖planarFibreDirection r‖^2=1+4*r^2 := by
    apply h.trans
    change (-2*r)^2+1^2=1+4*r^2
    ring
  rw [← hsq,Real.sqrt_sq (norm_nonneg _)]

/-- The full normalized leading planar minimax has exactly the coefficient
B*r*sqrt(1+4r²)*M_F(r), over every true tensor and every data-only output policy.
Article: main_krylov, thm:Fplanar, the sharp leading minimax formula. -/
theorem planar_policyMinimax (r B : ℝ) (hr : 0≤r) (hB : 0≤B) :
    policyMinimax r ((B*r) • planarFibreDirection r)=
      ENNReal.ofReal (B*r*Real.sqrt (1+4*r^2)*fibreMinimax r) := by
  rw [policyMinimax_eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hB hr),planarFibreDirection_norm]
  congr 1
  ring

end
end krylov.Tensor.BinaryCubic
