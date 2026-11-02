import krylov.Methods.DirectBroydenOperator
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), genuine chronological direct Broyden models.
Use: derive actual model positivity, real recursive curvature domains and
primitive joint regularity before the full perturbation comparison.
Source: literal direct update, its proved completed-square positivity and
true finite observed-pair recursion; no model correctness field is assumed. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual direct Broyden model from genuine chronological observed
pairs, stored newest first, with the original interpolation schedule.
Use: every later model and comparison is this actual recursive update.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenOperatorModel (B0 : E →L[ℝ] E) (phi : ℕ → ℝ) : List (E × E) → E →L[ℝ] E
  | [] => B0
  | (s,y)::W => directBroydenOperatorUpdate (directBroydenOperatorModel B0 phi W) s y (phi W.length)

/-- The true chronological native direct-model inverse-curvature domains.
Use: these are actual observed scalars, not supplied perturbation estimates
or assumed positive model outputs.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def DirectBroydenPivots (B0 : E →L[ℝ] E) (phi : ℕ → ℝ) : List (E × E) → Prop
  | [] => True
  | (s,y)::W =>
    inner ℝ s (directBroydenOperatorModel B0 phi W s)≠0 ∧ inner ℝ s y≠0 ∧ DirectBroydenPivots B0 phi W

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The actual direct chronological model remains symmetric and strictly
positive from a positive initial model and positive genuine pair curvatures.
Use: every original convex schedule has actual native positive old models;
the statement even holds for all nonnegative interpolation schedules.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: chronological induction applies the proved literal one-step symmetry
and completed-square positivity to the actual recursive older model. -/
theorem directBroydenOperatorModel_positive (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (phi : ℕ → ℝ) (hphi : ∀ i,0≤phi i) (W : List (E × E))
    (hpair : ∀ p∈W,0 < inner ℝ p.1 p.2) :
    (directBroydenOperatorModel B0 phi W).toLinearMap.IsSymmetric ∧
      ∀ w : E,w≠0 → 0 < inner ℝ w (directBroydenOperatorModel B0 phi W w) := by
  induction W with
  | nil => exact ⟨hB0,hpos⟩
  | cons p W ih =>
    have hold := ih (fun q hq => hpair q (List.mem_cons_of_mem p hq))
    change (directBroydenOperatorUpdate (directBroydenOperatorModel B0 phi W) p.1 p.2 (phi W.length)).toLinearMap.IsSymmetric ∧ _
    rw [directBroydenOperatorUpdate_toLinearMap]
    exact ⟨directBroydenUpdate_symmetric _ hold.1 _ _ _,
      directBroydenUpdate_positive _ hold.1 hold.2 _ _ (hpair p List.mem_cons_self) _ (hphi _)⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Every real native direct curvature denominator is nonzero on the
original positive observed-pair class and nonnegative actual schedules.
Use: native joint regularity receives its inverse domains from genuine
chronological positivity, rather than a model-pivot premise.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual positive secant curvature makes the true step nonzero. The
proved actual older positive model gives its own strictly positive curvature;
repeat through the genuine recursive tail. -/
theorem directBroydenOperatorModel_pivots (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (phi : ℕ → ℝ) (hphi : ∀ i,0≤phi i) (W : List (E × E))
    (hpair : ∀ p∈W,0 < inner ℝ p.1 p.2) : DirectBroydenPivots B0 phi W := by
  induction W with
  | nil => trivial
  | cons p W ih =>
    have hp := hpair p List.mem_cons_self
    have htail : ∀ q∈W,0 < inner ℝ q.1 q.2 := fun q hq => hpair q (List.mem_cons_of_mem p hq)
    have hs : p.1≠0 := by intro hz;rw [hz,inner_zero_left] at hp;exact lt_irrefl _ hp
    have hold := directBroydenOperatorModel_positive B0 hB0 hpos phi hphi W htail
    exact ⟨(hold.2 p.1 hs).ne',hp.ne',ih htail⟩

/-- The genuine accumulated direct model is C-r jointly in its primitive
initial operator, complete observed pair data and interpolation coordinates,
at every actual recursive curvature domain.
Use: interpolation schedules may vary arbitrarily with the perturbation;
the eventual boundedness argument controls them through a compact parameter
cube using this genuine joint regularity, not a smooth-schedule assumption.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: real chronological induction derives the actual older-model regularity
and composes the proved genuine one-step bounded-operator calculus at the
actual two measured curvatures. Original getter/map lengths preserve each
true chronological interpolation index. -/
theorem directBroydenOperatorModel_contDiffAt {r : WithTop ℕ∞}
    (B0 : X → E →L[ℝ] E) (phi : X → ℕ → ℝ) (W : List (X → E × E)) (x : X)
    (hB0 : ContDiffAt ℝ r B0 x)
    (hpairs : ∀ f∈W,ContDiffAt ℝ r (fun z => (f z).1) x ∧ ContDiffAt ℝ r (fun z => (f z).2) x)
    (hphi : ∀ i<W.length,ContDiffAt ℝ r (fun z => phi z i) x)
    (hpiv : DirectBroydenPivots (B0 x) (phi x) (W.map (fun f => f x))) :
    ContDiffAt ℝ r (fun z => directBroydenOperatorModel (B0 z) (phi z) (W.map (fun f => f z))) x := by
  induction W with
  | nil => exact hB0
  | cons f W ih =>
    have h := ih (fun g hg => hpairs g (List.mem_cons_of_mem f hg))
      (fun i hi => hphi i (by simp only [List.length_cons];omega)) hpiv.2.2
    have hs := (hpairs f List.mem_cons_self).1
    have hy := (hpairs f List.mem_cons_self).2
    have hq := hphi W.length (by simp only [List.length_cons];omega)
    have ha : inner ℝ (f x).1 (directBroydenOperatorModel (B0 x) (phi x) (W.map (fun g => g x)) (f x).1)≠0 := hpiv.1
    have hb : inner ℝ (f x).1 (f x).2≠0 := hpiv.2.1
    have hu := directBroydenOperatorUpdate_contDiffAt
      (fun z => directBroydenOperatorModel (B0 z) (phi z) (W.map (fun g => g z)))
      (fun z => (f z).1) (fun z => (f z).2) (fun z => phi z W.length) x h hs hy hq ha hb
    simpa only [List.map_cons,directBroydenOperatorModel,List.length_map] using hu

end
end krylov.Methods
