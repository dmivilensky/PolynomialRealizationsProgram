import krylov.Reference.Energy
import krylov.LinearAlgebra.SymmetricBall

/-!
Article: main_krylov, prop:conv, exact conversion of perturbation information.
Use: distinguish independent error-model injections from cumulative secant
increments; prove their exact telescoping relation and actual minimum image norm.
Source: finite telescoping and the already proved symmetric-ball image theorem (Rump03).
-/

namespace krylov.Realization
noncomputable section
open Finset krylov.Reference krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact accumulated canonical injection produced by secant increments along actual steps.
Use: the segment operator at step k contains precisely the earlier increments.
Article: main_krylov, prop:conv, ι̂_j=Σ_(k<j)(Σ_(l<k)Ê_l)σ_k. -/
def secantInjection (D : ℕ → E →L[ℝ] E) (s : ℕ → E) (j : ℕ) : E :=
  ∑ k∈range j, ∑ l∈range k, D l (s k)

/-- The exact injection recursion adds the true cumulative segment perturbation at its actual step.
Use: error and secant models are compared before taking any variation.
Article: main_krylov, prop:conv, cumulative injection update.
Proof: split the final actual step of the finite sum. -/
theorem secantInjection_succ (D : ℕ → E →L[ℝ] E) (s : ℕ → E) (j : ℕ) :
    secantInjection D s (j+1)=secantInjection D s j+∑ l∈range j, D l (s j) :=
  sum_range_succ _ j

/-- The actual cumulative secant injection equals the exact sum of remaining displacement differences.
Use: the source's conversion formula follows before inserting a first-order reference approximation.
Article: main_krylov, prop:conv, Σ_lÊ_l(e_j−e_(l+1)).
Proof: induct on the actual finite horizon; the newest increment multiplies
zero and the old contributions telescope by linearity of their genuine operator actions. -/
theorem secantInjection_telescopes (D : ℕ → E →L[ℝ] E) (e : ℕ → E) (j : ℕ) :
    secantInjection D (fun k => e (k+1)-e k) j=
      ∑ l∈range j, D l (e j-e (l+1)) := by
  -- Exchange the cumulative injection sums by their finite recursion, keeping the last zero term explicit.
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [secantInjection_succ, ih, sum_range_succ]
    simp only [sub_self, map_zero, add_zero]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro l _
    rw [← map_add]
    congr 1
    abel

/-- Replacing actual steps by reference steps has an explicit finite product-error bound.
Use: first-order increments and first-order trajectory errors give precisely a quadratic conversion remainder.
Article: main_krylov, prop:conv, O(ω²) remainder.
Proof: subtract the actual finite injections, move differences through each
linear operator, then sum their true operator-norm action bounds. -/
theorem secantInjection_difference_le (D : ℕ → E →L[ℝ] E) (s t : ℕ → E) (j : ℕ) :
    ‖secantInjection D s j-secantInjection D t j‖≤
      ∑ k∈range j, ∑ l∈range k, ‖D l‖*‖s k-t k‖ := by
  -- Every omitted first-order trajectory change is multiplied by an actual secant increment.
  unfold secantInjection
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k _
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  exact sum_le_sum fun l _ => by rw [← map_sub]; exact (D l).le_opNorm _

variable [CompleteSpace E]

/-- The minimum norm of a genuine self-adjoint secant perturbation with a prescribed nonzero step image.
Use: converts an error-model injection difference to its actual sharp canonical secant cost.
Article: main_krylov, prop:conv, ‖ι̂_(i+1)−ι̂_i‖/‖σ_i‖.
Source: the proved symmetric-ball identity, with its actual reflection witness.
Proof: the operator action inequality bounds every candidate below; the
existing self-adjoint image construction attains the exact ratio. -/
theorem minimum_secant_norm (s v : E) (hs : s≠0) :
    IsLeast {r : ℝ | ∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ T s=v ∧ ‖T‖=r} (‖v‖/‖s‖) := by
  have hn : 0<‖s‖ := norm_pos_iff.mpr hs
  have hratio : 0≤‖v‖/‖s‖ := div_nonneg (norm_nonneg _) hn.le
  obtain ⟨T,hT,ht,hv⟩ := exists_selfAdjoint_image s v hratio (by rw [div_mul_cancel₀ _ hn.ne'])
  have he : ‖T‖=‖v‖/‖s‖ := le_antisymm ht
    ((div_le_iff₀ hn).mpr (by rw [← hv]; exact T.le_opNorm s))
  refine ⟨⟨T,hT,hv,he⟩,?_⟩
  rintro r ⟨U,_,hu,rfl⟩
  exact (div_le_iff₀ hn).mpr (by rw [← hu]; exact U.le_opNorm s)

variable {n : ℕ}

/-- On the actual CG reference the cumulative secant injection has the printed canonical error-difference form.
Use: supplies the exact reference term in the first-order budget conversion.
Article: main_krylov, prop:conv, canonical CG reference.
Proof: actual CG canonical steps are exactly consecutive canonical error differences,
and the general finite telescoping conversion applies to those actual vectors. -/
theorem cg_secantInjection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (D : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (j : ℕ) : secantInjection D (canonicalCGStep base g) j=
      ∑ l∈range j, D l (cgCanonicalError base g j-cgCanonicalError base g (l+1)) := by
  have hs : canonicalCGStep base g=fun k => cgCanonicalError base g (k+1)-cgCanonicalError base g k := by
    funext k
    rw [cgCanonicalError_succ base hb, add_sub_cancel_left]
  rw [hs]
  exact secantInjection_telescopes D _ j

end
end krylov.Realization
