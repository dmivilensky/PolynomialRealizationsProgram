import krylov.Functions.HilbertPlaneTranscript
import krylov.Functions.PlanarFiniteMinimax

/-!
Article: main_krylov, prop:Fcycle(iii), unrestricted full-space information lower bound.
Use: reduce every actual rich-transcript output to a genuine binary
observation policy, then project its actual gradient. Source: exact scalar
transcript equality and the attained true planar all-policy information radius.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual output constant on genuine binary observation fibres
factors through an unrestricted observation-only policy. Article: prop:Fcycle(iii). -/
theorem binary_observation_policy {V : Type*} [Zero V] (r : ℝ)
    (output : krylov.Tensor.BinaryCubic → V)
    (houtput : ∀ t u : krylov.Tensor.BinaryCubic, observe r t=observe r u → output t=output u) :
    ∃ policy : Observation → V, ∀ t : krylov.Tensor.BinaryCubic, policy (observe r t)=output t := by
  classical
  let policy := fun o : Observation =>
    if h : ∃ t : krylov.Tensor.BinaryCubic, observe r t=o then output h.choose else 0
  refine ⟨policy,?_⟩
  intro t
  have hex : ∃ u : krylov.Tensor.BinaryCubic, observe r u=observe r t := ⟨t,rfl⟩
  simp only [policy,dite_eq_left hex]
  exact houtput _ t hex.choose_spec

/-- The actual worst full-space gradient of an arbitrary rich-transcript
output, allowing every full-space displacement and unbounded policies.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlanePolicyWorst (e h m : E) (p r : ℝ) (x s : ℕ → E) (N : ℕ)
    (policy : FunctionSearchTranscript E N → E) : ℝ≥0∞ :=
  ⨆ t : {t : krylov.Tensor.BinaryCubic // t.InBall},
    ENNReal.ofReal ‖gradient (hilbertPlaneObjective e h m p r t.val)
      (policy (functionSearchTranscript (hilbertPlaneObjective e h m p r t.val) x s N))‖

/-- The complete actual planar information coefficient is a lower bound
for every unrestricted full-space output using all actual observed values,
all actual observed gradients, and even all complete line restrictions.
No output localization or assumed policy factorization is used.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlanePolicyWorst_lower_quartic (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (r : ℝ) (hr : 0<r) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ x s : ℕ → E, ∀ N : ℕ,
      (∀ i≤N, (inner ℝ e (x i)=0 ∧ inner ℝ h (x i)=0) ∨
        (inner ℝ e (x i)=p ∧ inner ℝ h (x i)=0) ∨ (inner ℝ e (x i)=p ∧ inner ℝ h (x i)=r*p)) →
      (∀ i<N, (inner ℝ h (x i)=0 ∧ inner ℝ h (s i)=0) ∨
        (inner ℝ e (x i)=p ∧ inner ℝ e (s i)=0)) →
      ∀ policy : FunctionSearchTranscript E N → E,
        ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-C*p^4)≤
          hilbertPlanePolicyWorst e h m p r x s N policy := by
  obtain ⟨C,hC,hlower⟩ := planeCubicPolicyWorst_lower_quartic r hr
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ x s N hpoints hlines policy
  let output := fun t : krylov.Tensor.BinaryCubic =>
    hilbertPlaneProject e h (policy (functionSearchTranscript (hilbertPlaneObjective e h m p r t) x s N))
  obtain ⟨q,hq⟩ := binary_observation_policy r output (by
    intro t u hobs
    dsimp only [output]
    rw [hilbertPlaneObjective_transcript_equal e h m p r t u hobs x s N hpoints hlines])
  apply (hlower p hp hp₁ q).trans
  apply iSup_le
  intro t
  apply le_iSup_of_le t
  apply ENNReal.ofReal_le_ofReal
  rw [hq]
  exact hilbertPlaneGradient_norm_lower e h m he hh heh hm p r t.val _

end
end krylov.Functions
