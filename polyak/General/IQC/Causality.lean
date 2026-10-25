import polyak.General.IQC.Sequence

/-! Article: Appendix D, Lemma homotopy. Strict causality gives existence,
uniqueness and finite-prefix dependence without a summability assumption. -/
noncomputable section
namespace polyak.General.IQC

variable {E : Type*} [Zero E] [Add E]

def Causal (F : (ℕ → E) → ℕ → E) : Prop :=
  ∀ N x y,(∀ k<N,x k=y k) → ∀ k<N,F x k=F y k

def StrictCausal (F : (ℕ → E) → ℕ → E) : Prop :=
  ∀ k x y,(∀ j<k,x j=y j) → F x k=F y k

def causalSolve (F : (ℕ → E) → ℕ → E) (f : ℕ → E) (n : ℕ) : E :=
  Nat.strongRecOn n (fun k rec => F (fun j => if h : j<k then rec j h else 0) k+f k)

theorem causalSolve_equation {F : (ℕ → E) → ℕ → E} (hF : StrictCausal F)
    (f : ℕ → E) (n : ℕ) : causalSolve F f n=F (causalSolve F f) n+f n := by
  unfold causalSolve
  rw [Nat.strongRecOn_eq]
  congr 1
  apply hF
  intro j hj
  rw [dite_eq_left hj]

theorem causalSolve_unique {F : (ℕ → E) → ℕ → E} (hF : StrictCausal F)
    (f x : ℕ → E) (hx : ∀ k,x k=F x k+f k) : x=causalSolve F f := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hx n,causalSolve_equation hF]
    congr 1
    exact hF n x (causalSolve F f) ih

theorem causalSolve_causal {F : (ℕ → E) → ℕ → E} (hF : StrictCausal F) :
    Causal (causalSolve F) := by
  intro N f g hfg k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [causalSolve_equation hF,causalSolve_equation hF,hfg k hk]
    congr 1
    apply hF
    intro j hj
    exact ih j hj (hj.trans hk)

omit [Zero E] [Add E] in
theorem StrictCausal.comp {G F : (ℕ → E) → ℕ → E}
    (hG : StrictCausal G) (hF : Causal F) : StrictCausal (G ∘ F) := by
  intro k x y hxy
  exact hG k (F x) (F y) (hF k x y hxy)

end polyak.General.IQC
