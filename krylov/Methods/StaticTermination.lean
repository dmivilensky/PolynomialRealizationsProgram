import krylov.Methods.QuadraticCycles

/-!
Article: main_krylov, prop:dict(iii), exact static-drift termination.
Use: derive the actual physical iterate and actual finite stopping for every
CG-consistent policy, including arbitrary finite adaptive correction trees.
Source: linear oracle telescoping and the already proved true active-atom CG stopping criterion.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual correction gradient equals its initial gradient plus the operator applied to its total movement.
Use: physical quadratic gradient balance holds for every finite adaptive correction tree.
Article: main_krylov, def:classes(M) and prop:dict(iii).
Proof: induct on the executed finite decision tree; its actual linear oracle
update telescopes with the recursively executed actual movements. -/
theorem runCorrections_gradient (p : CorrectionTree E) (Q : E →L[ℝ] E) (g : E) :
    (runCorrections p Q g).gradient=g+Q (runCorrections p Q g).movement := by
  induction p generalizing g with
  | done => simp only [runCorrections, map_zero, add_zero]
  | query u next ih =>
    change (runCorrections (next (g+Q u)) Q (g+Q u)).gradient=_
    rw [ih]
    change (g+Q u)+Q _=g+Q (u+_)
    rw [map_add, add_assoc]

/-- Every actual static probed-policy run has the true physical quadratic gradient of its actual iterate.
Use: the static consistency argument does not silently identify gradients with points.
Article: main_krylov, prop:dict(iii).
Proof: each actual exact-search step and each actual adaptive correction
contribute their true linear operator actions to the current gradient and their true movements to the iterate. -/
theorem methodRun_quadratic_gradient (m : ProbedMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    H.gradient=g+Q H.displacement := by
  -- The correction balance is valid without consistency, zero coefficients or fixed correction schedules.
  induction k with
  | zero => simp only [methodRun, History.gradient, History.displacement, List.map_nil, List.sum_nil, map_zero, add_zero]
  | succ k ih =>
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    let d := m.direction H
    let z := Q d
    let r := runCorrections (m.correction H z) Q (searchedGradient H.gradient d z)
    have hr : r.gradient=searchedGradient H.gradient d z+Q r.movement := runCorrections_gradient _ Q _
    change r.gradient=g+Q ((lineLength H.gradient d z • d+r.movement)+H.displacement)
    rw [hr, searchedGradient, ih, map_add, map_add, map_smul]
    dsimp only [H, z]
    abel

/-- A genuinely positive quadratic operator is injective.
Use: equality of actual quadratic gradients implies equality of actual physical iterates.
Article: main_krylov, prop:dict(iii), positive static quadratic.
Proof: a nonzero kernel difference would have strictly positive energy and zero operator action. -/
theorem positive_operator_injective (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) : Function.Injective Q := by
  intro x y hxy
  by_contra hne
  have he := hpos (x-y) (sub_ne_zero.mpr hne)
  rw [map_sub, hxy, sub_self, inner_zero_right] at he
  exact (lt_irrefl 0 he)

/-- Every actual static CG-consistent policy has the actual true CG physical iterate.
Use: the result quantifies over arbitrary actual adaptive policies and all permitted positive direction scales.
Article: main_krylov, prop:dict(iii).
Proof: both real trajectories have the proved actual quadratic gradient balance,
consistency identifies their gradients, and true positive-operator injectivity identifies their points. -/
theorem quadratic_displacement_eq_cg (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    (methodRun m (fun _ => Q) (fun _ => Q) g k).displacement=CG.displacement Q g k := by
  apply positive_operator_injective Q hpos
  apply add_left_cancel (a := g)
  rw [← methodRun_quadratic_gradient, ← CG.gradient_displacement]
  exact quadratic_gradient_eq_cg m hm Q hQ hpos g k

/-- Every actual CG-consistent policy terminates exactly at the active atom count of any static positive quadratic.
Use: applies equally to a static shifted quadratic; no smallness of the static drift is required.
Article: main_krylov, prop:dict(iii), static drift has zero terminal error.
Proof: the actual executed gradient equals the true CG gradient, whose exact
active-spectrum stopping theorem includes repeated eigenvalues and initially absent spectral coordinates. -/
theorem cgConsistent_static_stopping {n : ℕ} (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g k).gradient=0 ↔
      referenceAtomCount base hb g≤k := by
  rw [quadratic_gradient_eq_cg m hm _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2]
  exact cg_stopping_iff base hb g k

end
end krylov.Methods
