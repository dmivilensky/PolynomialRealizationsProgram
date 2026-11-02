import krylov.Methods.DirectBroydenPerturbation
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), full native direct model induction.
Use: derive the original first-order vector-secant and second-order latest
scalar model comparisons for every genuine chronological prefix.
Source: primitive perturbation limits, proved compact native bounds and
the actual direct update's exact secant and quadratic cross-pair formulas.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine native direct model is eventually symmetric under the
original primitive perturbation assumptions, including the final model.
Use: the full scalar compression follows from the genuine newer-column
comparison by actual model symmetry.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the initial model is symmetric; for every later prefix the native
previous symmetry and literal symmetric update give the actual result. -/
theorem directBroydenPerturbation_symmetric {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (k : ℕ) (hk : k≤p) :
    ∀ᶠ z in l,(directBroydenPerturbedModel D z k).toLinearMap.IsSymmetric := by
  cases k with
  | zero => exact Eventually.of_forall (fun _ => D.initial_symmetric)
  | succ k =>
    filter_upwards [(directBroydenPerturbation_model_bounds D k (by omega)).2.2] with z hz
    change (directBroydenNative D.initial (D.parameter z) (directBroydenPerturbedPairs D z) (k+1)).toLinearMap.IsSymmetric
    rw [directBroydenNative_succ,directBroydenOperatorUpdate_toLinearMap]
    exact directBroydenUpdate_symmetric _ hz.1 _ _ _

/-- The literal native chronological direct Broyden recursion has all
old vector secant errors of first order and all newer-observation scalar
model errors of second order under precisely the primitive perturbation
assumptions; no regularity of the original convex schedule is needed.
Use: closes the genuine model-comparison induction of the source.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: genuine compact parameter bounds derive all actual model and
curvature factors. The inductive old vector secants derive first-order
new/old cross pairings. The actual vector update has one such factor and
the actual scalar update has two. The newest true secant is exact. -/
theorem directBroyden_native_comparison {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (k : ℕ) (hk : k≤p) :
    (∀ i<k,(fun z => directBroydenPerturbedModel D z k (D.step z i)-D.image z i) =O[l] t) ∧
    (∀ i<k,∀ j<k,i≤j →
      (fun z => inner ℝ (D.step z i) (directBroydenPerturbedModel D z k (D.step z j))-
        inner ℝ (D.step z i) (D.image z j)) =O[l] (fun z => t z^2)) := by
  induction k with
  | zero => exact ⟨fun i hi => by omega,fun i hi => by omega⟩
  | succ k ih =>
    have hk0 : k<p := by omega
    have hold := ih (by omega)
    have hb := directBroydenPerturbation_model_bounds D k hk0
    have hp := directBroydenPerturbation_pair_bounds D k hk0
    have hsym : ∀ᶠ z in l,(directBroydenPerturbedModel D z k).toLinearMap.IsSymmetric := hb.2.2.mono (fun _ h => h.1)
    have hupdate (z : α) : directBroydenPerturbedModel D z (k+1)=
        directBroydenOperatorUpdate (directBroydenPerturbedModel D z k) (D.step z k) (D.image z k) (D.parameter z k) :=
      directBroydenNative_succ _ _ _ _
    have hcross (i : ℕ) (hi : i<k) :
        (fun z => inner ℝ (D.step z k) (directBroydenPerturbedModel D z k (D.step z i))) =O[l] t := by
      have he := real_inner_bigO (fun z => D.step z k)
        (fun z => directBroydenPerturbedModel D z k (D.step z i)-D.image z i) _ _ hp.1 (hold.1 i hi)
      have he' : (fun z => inner ℝ (D.step z k)
          (directBroydenPerturbedModel D z k (D.step z i)-D.image z i)) =O[l] t := by
        simpa only [one_mul] using he
      exact (he'.add (directBroydenPerturbation_cross D k i hk0 (by omega) (by omega))).congr_left (fun z => by
        rw [inner_sub_right]
        ring)
    have hycross (i : ℕ) (hi : i<k) :
        (fun z => inner ℝ (D.image z k) (D.step z i)) =O[l] t :=
      (directBroydenPerturbation_cross D i k (by omega) hk0 (by omega)).congr_left
        (fun z => real_inner_comm (D.image z k) (D.step z i))
    have hnew : ∀ᶠ z in l,directBroydenPerturbedModel D z (k+1) (D.step z k)=D.image z k := by
      filter_upwards [hb.2.2] with z hz
      rw [hupdate]
      exact directBroydenUpdate_secant _ _ _ _ hz.2.1 hz.2.2
    constructor
    · intro i hi
      by_cases hik : i<k
      · have hu := directBroydenOperatorUpdate_vector_bigO
          (fun z => directBroydenPerturbedModel D z k) (fun z => D.step z k)
          (fun z => D.image z k) (fun z => D.step z i) (fun z => D.parameter z k) t
          hsym hb.1 hp.1 hp.2.1 hp.2.2.2.1 hb.2.1 hp.2.2.1 (hcross i hik) (hycross i hik)
        exact (hu.add (hold.1 i hik)).congr_left (fun z => by rw [← hupdate];abel)
      · have he : i=k := by omega
        subst i
        apply IsBigO.of_bound 0
        filter_upwards [hnew] with z hz
        simp only [hz,sub_self,norm_zero,zero_mul,le_refl]
    · intro i hi j hj hij
      by_cases hjk : j<k
      · have hik : i<k := by omega
        have hu := directBroydenOperatorUpdate_scalar_bigO
          (fun z => directBroydenPerturbedModel D z k) (fun z => D.step z k)
          (fun z => D.image z k) (fun z => D.step z i) (fun z => D.step z j)
          (fun z => D.parameter z k) t hsym hb.1 hp.1 hp.2.1 hp.2.2.2.1 hb.2.1 hp.2.2.1
          (hcross i hik) (hcross j hjk) (hycross i hik) (hycross j hjk)
        exact (hu.add (hold.2 i hik j hjk hij)).congr_left (fun z => by rw [← hupdate];ring)
      · have he : j=k := by omega
        subst j
        apply IsBigO.of_bound 0
        filter_upwards [hnew] with z hz
        simp only [hz,sub_self,norm_zero,zero_mul,le_refl]

end
end krylov.Methods
