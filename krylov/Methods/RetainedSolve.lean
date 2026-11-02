import krylov.Methods.Windows

/-!
Article: main_krylov, lem:consistent(a), the actual retained-window solve.
Use: instantiate the arbitrary selected-reference-step theorem with the
newest-first lists that the implemented algorithms actually retain.
Source: the retained-newest-pair CG identity, as in KoldaEtAl98.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The data-only direction computed from an actual finite observed pair window.
Use: the same solve is used by FC and every probed repeated-correction policy.
Article: main_krylov, alg:fc, (YᵀS)β=Yᵀg. -/
def windowDirection (W : List (E × E)) (g : E) : E :=
  conjugacyDirection (windowSteps W) (windowImages W) g

/-- A retained reference list really contains the stated chronological CG pair.
Use: transport the actual list implementation to the generic independent-family solve.
Article: main_krylov, lem:consistent(a), retained pairs.
Proof: taking a newest suffix preserves its entries, and the full actual transcript has the proved age formula. -/
theorem retained_pair (Q : E →L[ℝ] E) (g : E) (k m : ℕ)
    (i : Fin ((referencePairs Q g k).take m).length) :
    ((referencePairs Q g k).take m).get i=
      (referenceStep Q g (k-1-i.val), Q (referenceStep Q g (k-1-i.val))) := by
  have hi : i.val<k := by
    have := i.isLt
    simp only [List.length_take, referencePairs_length] at this
    omega
  simpa only [List.get_eq_getElem, List.getElem_take] using referencePairs_get Q g k i.val hi

/-- The actual newest-suffix direction equals the true CG direction whenever the current gradient is nonzero.
Use: discharge concrete policy consistency from its actual stored reference transcript.
Article: main_krylov, lem:consistent(a), all positive sliding and full windows.
Proof: the age-to-time map is injective and retains time k−1; the general
computed conjugacy uniqueness theorem then identifies the actual block solve. -/
theorem windowDirection_reference (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : CG.gradient Q g k≠0) (hm : 0<k → 0<m) :
    windowDirection ((referencePairs Q g k).take m) (CG.gradient Q g k)=CG.direction Q g k := by
  -- Once CG has stopped it stays stopped, so a nonzero current residual certifies the whole earlier prefix.
  have hpre : ∀ i<k, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hg (CG.gradient_eq_zero_of_le Q g hz hi.le)
  let W := (referencePairs Q g k).take m
  have hr (i : Fin W.length) := retained_pair Q g k m i
  have hlen : W.length=min m k := by simp only [W, List.length_take, referencePairs_length]
  have hi (i : Fin W.length) : i.val<k := by have := i.isLt; simp only [hlen] at this; omega
  change conjugacyDirection _ _ _=_
  have hs : windowSteps W=fun i => referenceStep Q g (k-1-i.val) := by
    funext i; exact congrArg Prod.fst (hr i)
  have hy : windowImages W=fun i => Q (referenceStep Q g (k-1-i.val)) := by
    funext i; exact congrArg Prod.snd (hr i)
  rw [hs, hy]
  apply conjugacyDirection_reference Q hQ hpos g k hpre
  · intro i j hij
    change k-1-i.val=k-1-j.val at hij
    apply Fin.ext
    have := hi i
    have := hi j
    omega
  · intro i; have := hi i; omega
  · intro hk
    have hm' := hm hk
    have hzero : 0<W.length := by rw [hlen]; omega
    exact ⟨⟨0,hzero⟩, by simp only [Nat.sub_zero]; omega⟩

/-- The actually computed window direction is zero on zero observed data, including singular stored models.
Use: all concrete policies agree with the stopped CG tail without an artificial inverse assumption.
Article: main_krylov, lem:consistent, zero residual.
Proof: the generic computed right-hand side vanishes. -/
theorem windowDirection_zero (W : List (E × E)) : windowDirection W (0 : E)=0 :=
  conjugacyDirection_zero _ _

/-- The actual newest-suffix direction agrees with CG also on solved tails.
Use: concrete policy consistency is total, while nonsingularity is asserted only on the active prefix.
Article: main_krylov, lem:consistent(a), stopping convention.
Proof: separate the actual zero residual before applying retained-window uniqueness. -/
theorem windowDirection_reference_all (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hm : CG.gradient Q g k≠0 → 0<k → 0<m) :
    windowDirection ((referencePairs Q g k).take m) (CG.gradient Q g k)=CG.direction Q g k := by
  by_cases hg : CG.gradient Q g k=0
  · rw [hg, windowDirection_zero, direction_zero_of_gradient Q g k hg]
  · exact windowDirection_reference Q hQ hpos g k m hg (hm hg)

end
end krylov.Methods
