import krylov.Envelope.GradientJetLift
import krylov.Envelope.KrylovFlags
import krylov.Stability.AnalyticCG
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Use: construct the actual finite CG-gradient orthogonal projector and prove
its genuine current-direction identity and local operator continuity, for
the real absorbed-scenario quadratic shadow construction.
Source: standard real finite orthogonal projection by actual orthogonal
CG gradients, proved true Krylov flags and actual reference CG continuity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Stability
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true finite CG-gradient projection represented by actual normalized rank-one gradient operators.
Use: The true finite CG-gradient projection represented by actual normalized rank-one gradient operators.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: Sum the genuine orthogonal reference-gradient rank-one coordinate maps with their true squared-energy denominators. -/
def gradientProjection (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E →L[ℝ] E :=
  ∑ i∈Finset.range (k+1), (‖CG.gradient Q g i‖^2)⁻¹ •
    InnerProductSpace.rankOne ℝ (CG.gradient Q g i) (CG.gradient Q g i)

/-- The actual finite CG-gradient projector acts by the genuine reference-gradient coordinate lift.
Use: The actual finite CG-gradient projector acts by the genuine reference-gradient coordinate lift.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: Expand the real rank-one operator actions and true finite sum. -/
theorem gradientProjection_apply (Q : E →L[ℝ] E) (g : E) (k : ℕ) (v : E) :
    gradientProjection Q g k v=gradientJetLift Q g (CG.gradient Q g) k v := by
  simp only [gradientProjection,_root_.sum_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    gradientJetLift,smul_smul,div_eq_mul_inv,mul_comm]
  rfl

/-- The actual active CG-gradient projector fixes every vector of its true polynomial Krylov flag.
Use: The actual active CG-gradient projector fixes every vector of its true polynomial Krylov flag.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: The genuine nonzero CG gradients span that real flag; true orthogonality recovers each actual gradient and linearity extends to the full actual span. -/
theorem gradientProjection_self (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0) {v : E} (hv : v∈CG.krylovSpace Q g (k+1)) :
    gradientProjection Q g k v=v := by
  -- The genuine nonzero CG lines identify the actual gradient span with the true polynomial Krylov flag.
  have hline (i : ℕ) (hi : i<k+1) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hpre j (by omega))) (hpre i (by omega))).2.1.ne'
  rw [CG.krylovSpace_eq_span_gradients Q g (k+1) hline] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,hi,rfl⟩ := hv
    rw [gradientProjection_apply,gradientJetLift_gradient Q hQ hpos g (CG.gradient Q g) k hpre i (by change i<k+1 at hi;omega)]
  | zero => exact map_zero _
  | add u v _ _ hu hv => rw [map_add,hu,hv]
  | smul a v _ hv => rw [map_smul,hv]

/-- The actual active CG-gradient projector fixes every genuine earlier computed direction.
Use: The actual active CG-gradient projector fixes every genuine earlier computed direction.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: The true direction belongs to its actual Krylov flag, which lies in the real projection flag. -/
theorem gradientProjection_direction (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k j : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0) (hj : j≤k) :
    gradientProjection Q g k (CG.direction Q g j)=CG.direction Q g j := by
  apply gradientProjection_self Q hQ hpos g k hpre
  apply krylovSpace_mono Q g (show j+1≤k+1 by omega)
  exact cgDirection_mem_krylov Q g j (fun i hi => (CG.invariant_line_pos Q hpos g i
    (CG.invariant Q hQ hpos g i (fun l hl => hpre l (by omega))) (hpre i (by omega))).2.1.ne')

omit [NormedSpace ℝ X] in
/-- The true finite CG-gradient projector is continuous as an actual operator whenever its genuine active gradient columns are continuous.
Use: The true finite CG-gradient projector is continuous as an actual operator whenever its genuine active gradient columns are continuous.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: Each true nonzero gradient-energy inverse is continuous, and the genuine finite sum of real rank-one maps is continuous in the actual operator norm. -/
theorem gradientProjection_continuousAt (Q : X → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hG : ∀ i≤k, ContinuousAt (fun p => CG.gradient (Q p) (g p) i) x)
    (hpre : ∀ i≤k, CG.gradient (Q x) (g x) i≠0) :
    ContinuousAt (fun p => gradientProjection (Q p) (g p) k) x := by
  -- Actual nonzero reference energies make every genuine normalized rank-one operator continuous.
  apply tendsto_finsetSum
  intro i hi
  have hi' : i≤k := by have := Finset.mem_range.mp hi;omega
  have hg := hG i hi'
  have hc := (hg.norm.pow 2).inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre i hi')))
  exact hc.smul (((InnerProductSpace.rankOne ℝ (E := E) (F := E)).continuous.continuousAt.comp hg).clm_apply hg)
/-- The actual finite active CG-gradient projection inherits every genuine C-r regularity order of its true gradient columns.
Use: The actual finite active CG-gradient projection inherits every genuine C-r regularity order of its true gradient columns.
Article: main_krylov, apB:lem:mu(c), true moving quadratic shadow flags.
Proof: Rewrite genuine squared norms as actual self-inner-products, invert their true nonzero energies, and apply standard finite rank-one operator calculus. -/
theorem gradientProjection_contDiffAt (Q : X → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (r : WithTop ℕ∞) (hG : ∀ i≤k, ContDiffAt ℝ r (fun p => CG.gradient (Q p) (g p) i) x)
    (hpre : ∀ i≤k, CG.gradient (Q x) (g x) i≠0) :
    ContDiffAt ℝ r (fun p => gradientProjection (Q p) (g p) k) x := by
  -- Genuine squared gradient energies are smooth inner products, and their actual nonzero values permit the real reciprocal rule.
  apply ContDiffAt.sum
  intro i hi
  have hi' : i≤k := by have := Finset.mem_range.mp hi;omega
  have hg := hG i hi'
  have hn : inner ℝ (CG.gradient (Q x) (g x) i) (CG.gradient (Q x) (g x) i)≠0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpre i hi'))
  have hc := (hg.inner ℝ hg).inv hn
  convert! hc.smul (((InnerProductSpace.rankOne ℝ (E := E) (F := E)).contDiff.contDiffAt.comp x hg).clm_apply hg) using 1
  simp only [real_inner_self_eq_norm_sq]
  rfl

end
end krylov.Envelope
