import krylov.Methods.NazarethObserved
import krylov.Methods.DirectionInformation
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical and def:classes(M1), true Nazareth information.
Use: verify all-history observed-span admissibility of the actual measured
Lanczos direction and genuine recorded final correction.
Source: real history-tail monotonicity and linear combinations of genuinely
observed steps, gradients and secant differences; no operator is supplied. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Removing the newest actual record never enlarges the real observed span.
Use: source recurrences may reuse every genuinely observed older vector.
Article: main_krylov, prop:classical and def:classes.
Proof: inspect the empty case and reuse real observed-history span growth. -/
theorem historyTail_observedSpan_le (H : History E) : (historyTail H).observedSpan≤H.observedSpan := by
  rcases H with ⟨initial,records⟩
  cases records with
  | nil => exact le_rfl
  | cons r rs => exact (History.mk initial rs).observedSpan_cons r

/-- The true reconstructed previous trial direction is an available observed
vector on every supplied history, including empty or incompatible data.
Use: the genuine original Nazareth direction uses no hidden matrix information.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: its measured step is a real head pair generator; the old trial only
scales that genuinely observed vector. -/
theorem measuredTrialDirection_mem_observedSpan (trial : History E → ℝ) (H : History E) :
    measuredTrialDirection trial H∈H.observedSpan := by
  rcases H with ⟨initial,records⟩
  cases records with
  | nil => exact Submodule.zero_mem _
  | cons r rs =>
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Or.inl (Or.inl (Or.inr ⟨(r.step,r.gradient-(History.mk initial rs).gradient),List.mem_cons_self,rfl⟩))

/-- The true reconstructed previous direction image lies in the real
observed span on every history, without a quadratic or replay hypothesis.
Use: original measured Lanczos images are genuine available observations.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: subtract the real preceding gradient in the growing observed span
from the current actual gradient, then scale by its real old trial. -/
theorem measuredTrialImage_mem_observedSpan (trial : History E → ℝ) (H : History E) :
    measuredTrialImage trial H∈H.observedSpan := by
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ H.gradient_mem_observedSpan
    ((historyTail_observedSpan_le H) (historyTail H).gradient_mem_observedSpan))

/-- The literal original Nazareth computed direction respects the genuine
observed information restriction on every supplied complete history.
Use: its admissibility is proved for actual data-only decisions, including
all singular and incompatible totalized histories.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: all three actual direction terms combine only the proved available
current image, current direction and older direction; old history span is
contained in the genuine current observed span. -/
theorem nazarethDirection_mem_observedSpan (trial : History E → ℝ) (H : History E) :
    nazarethDirection trial H∈H.observedSpan := by
  cases hr : H.records with
  | nil =>
    rw [nazarethDirection,hr]
    change -H.initial∈H.observedSpan
    have hg := H.gradient_mem_observedSpan
    simpa only [History.gradient,hr] using H.observedSpan.neg_mem hg
  | cons r rs =>
    rw [nazarethDirection,hr]
    change trial (historyTail H) • (-measuredTrialImage trial H+
      (inner ℝ (measuredTrialImage trial H) (measuredTrialImage trial H)/
        inner ℝ (measuredTrialDirection trial H) (measuredTrialImage trial H)) • measuredTrialDirection trial H+
      (inner ℝ (measuredTrialImage trial (historyTail H)) (measuredTrialImage trial H)/
        inner ℝ (measuredTrialDirection trial (historyTail H)) (measuredTrialImage trial (historyTail H))) •
          measuredTrialDirection trial (historyTail H))∈H.observedSpan
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.neg_mem _ (measuredTrialImage_mem_observedSpan trial H))
      (Submodule.smul_mem _ _ (measuredTrialDirection_mem_observedSpan trial H)))
      (Submodule.smul_mem _ _ ((historyTail_observedSpan_le H) (measuredTrialDirection_mem_observedSpan trial _))))

/-- The actual original Nazareth one-gradient executor is span restricted
on all supplied histories.
Use: the named classical implementation belongs to the true source method class.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: its real trial only scales its proved available observed direction. -/
theorem nazarethMethod_spanRestricted (trial : History E → ℝ) :
    OneGradientSpanRestricted (nazarethMethod trial) :=
  fun H => H.observedSpan.smul_mem _ (nazarethDirection_mem_observedSpan trial H)

/-- The literal newly returned-gradient projection correction lies in the
span of the actual stored physical steps on every supplied history.
Use: original Nazareth final correction is a genuine unevaluated data-only
stored-step combination, without an unobserved matrix action.
Article: main_krylov, prop:classical(b), Nazareth77 equation (16).
Proof: every zipped record contributes a scalar multiple of its own actual
stored pair step; finite summation stays in the true stored-step span. -/
theorem recordedProjectionCorrection_mem_pairSpan (H : History E) :
    recordedProjectionCorrection H∈pairSpan H.pairs := by
  apply list_sum_mem
  intro v hv
  obtain ⟨rp,hrp,rfl⟩ := List.mem_map.mp hv
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rw [windowSteps_range]
  exact ⟨rp.2,(List.of_mem_zip hrp).2,rfl⟩

end
end krylov.Methods
