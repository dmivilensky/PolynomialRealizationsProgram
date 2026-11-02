import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, lem:terminal-fibre, the concrete CG reference needed by stage 1.
Use: reference directions come from an actual Fletcher--Reeves CG recurrence,
not fields containing the terminal data-fibre conclusion.
Source: HestenesStiefel52 and Meurant06; exact line search and the usual Fletcher--Reeves
residual-norm coefficient; zero denominators use the field's totalized division.
-/

namespace krylov.Reference
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual gradient/direction state of the concrete quadratic CG recurrence.
Use: define every reference query by running the genuine finite algorithm.
Article: main_krylov, s2:eq:cg, reference gradients and directions. -/
structure CGState (E : Type*) where
  /-- The actual gradient at this reference iterate. -/
  gradient : E
  /-- The actual current search direction. -/
  direction : E

/-- The actual exact line length computed from the observed gradient, direction and probe.
Use: the same data-only scalar is used by the reference and every probed method.
Article: main_krylov, def:classes(M), α=−⟨d,g⟩/⟨d,z⟩. -/
def lineLength (g d z : E) : ℝ := -inner ℝ d g/inner ℝ d z

/-- The actual post-search gradient computed from the observed probe.
Use: exact line search needs no additional unknown matrix action.
Article: main_krylov, def:classes(M), g′=g+αz. -/
def searchedGradient (g d z : E) : E := g+lineLength g d z • z

/-- Rescaling a true search direction and its actual probe rescales the exact line length reciprocally.
Use: CG consistency permits arbitrary positive multiples of its genuine directions.
Article: main_krylov, def:classes(M) and lem:terminal-fibre.
Proof: both scalar pairings scale explicitly; split the zero-curvature case
before clearing the remaining nonzero scalar denominators. -/
theorem lineLength_smul (g d z : E) {scale : ℝ} (hscale : scale≠0) :
    lineLength g (scale • d) (scale • z)=lineLength g d z/scale := by
  unfold lineLength
  simp only [real_inner_smul_left, real_inner_smul_right]
  by_cases hz : inner ℝ d z=0
  · simp only [hz, mul_zero, div_zero, zero_div]
  · field_simp

/-- The actual exact-search displacement is invariant under nonzero scaling of its direction and probe.
Use: all positive CG-consistent direction normalizations produce the same true reference step.
Article: main_krylov, lem:terminal-fibre, reference line step.
Proof: cancel the scalar direction factor against the reciprocal line-length factor. -/
theorem lineStep_smul (g d z : E) {scale : ℝ} (hscale : scale≠0) :
    lineLength g (scale • d) (scale • z) • (scale • d)=lineLength g d z • d := by
  rw [lineLength_smul g d z hscale, smul_smul, div_mul_cancel₀ _ hscale]

/-- The actual post-search gradient is invariant under nonzero direction/probe scaling.
Use: the terminal residual depends on the data fibre, not the policy's allowed positive direction scale.
Article: main_krylov, lem:terminal-fibre, common post-search gradient.
Proof: the true exact-search displacement coefficient on the actual probe is unchanged. -/
theorem searchedGradient_smul (g d z : E) {scale : ℝ} (hscale : scale≠0) :
    searchedGradient g (scale • d) (scale • z)=searchedGradient g d z := by
  simp only [searchedGradient]
  rw [lineLength_smul g d z hscale, smul_smul, div_mul_cancel₀ _ hscale]

/-- One concrete CG update using the actual observed operator action.
Use: queries the true operator on the current genuine CG direction.
Article: main_krylov, s2:eq:cg, standard quadratic CG recurrence. -/
def cgAdvance (T : E →L[ℝ] E) (s : CGState E) : CGState E :=
  let g := searchedGradient s.gradient s.direction (T s.direction)
  ⟨g, -g+(‖g‖^2/‖s.gradient‖^2) • s.direction⟩

/-- The concrete infinite CG run, with its actual stopping state totalized after breakdown.
Use: finite nondegenerate prefixes are selected by explicit reference hypotheses.
Article: main_krylov, s2:eq:cg, reference trajectory. -/
def cgRun (T : E →L[ℝ] E) (g : E) : ℕ → CGState E
  | 0 => ⟨g, -g⟩
  | k+1 => cgAdvance T (cgRun T g k)

/-- A concrete CG update depends on its unknown operator only through the actual current probe.
Use: transfer the actual reference to the shadow quadratic in the terminal data fibre.
Article: main_krylov, lem:terminal-fibre, reference-prefix induction.
Proof: substitute the single actual operator action in the explicit recurrence. -/
theorem cgAdvance_probe_eq (T Q : E →L[ℝ] E) (s : CGState E)
    (h : T s.direction=Q s.direction) : cgAdvance T s=cgAdvance Q s := by
  simp only [cgAdvance, h]

/-- Concrete CG runs agree through every prefix on which the true reference probes agree.
Use: shadow-reference equality is derived by running the actual CG recurrence.
Article: main_krylov, lem:terminal-fibre, unchanged quadratic reference prefix.
Proof: induction on the finite prefix, using the actual single-probe dependence of each CG update. -/
theorem cgRun_prefix_eq (T Q : E →L[ℝ] E) (g : E) (N : ℕ)
    (h : ∀ k<N, T (cgRun T g k).direction=Q (cgRun T g k).direction) :
    ∀ k≤N, cgRun T g k=cgRun Q g k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hle : k≤N := (Nat.le_succ k).trans hk
    rw [cgRun, cgRun, ← ih hle]
    exact cgAdvance_probe_eq T Q _ (h k (Nat.lt_of_succ_le hk))

end
end krylov.Reference
