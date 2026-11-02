import krylov.Convergence.ObservableRFCState
import krylov.Convergence.WindowAugmentation

/-!
Article: main_krylov, apG:Dunif, actual RFC probe augmentation.
Use: retain the true pairwise angle allowance when adjoining a genuinely
image-conjugate searched direction to the real stored window.
Source: measured conjugacy and relative observed secant errors. No
independence of the augmented window is assumed.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- True image conjugacy bounds every new normalized probe pairing;
the old actual angular bound is retained exactly.
Article: main_krylov, apG:Dunif. -/
theorem observable_probe_angles (s y : Fin p → E) (d : E)
    (hs : ∀ i,s i≠0) (hd : d≠0) (eta delta : ℝ) (hmargin : eta≤delta)
    (hy : ∀ i,‖y i-s i‖≤eta*‖s i‖) (ho : ∀ i,inner ℝ (y i) d=0)
    (hangle : ∀ i j,i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤delta) :
    ∀ i j : Fin (p+1),i≠j →
      |inner ℝ (unitWindow (Fin.cons d s) i) (unitWindow (Fin.cons d s) j)|≤delta := by
  have hp (i : Fin p) : |inner ℝ (unitWindow s i) (‖d‖⁻¹ • d)|≤delta :=
    (observed_conjugacy_unit_pairing (s i) (y i) d (hs i) hd (hy i) (ho i)).trans hmargin
  have he : unitWindow (Fin.cons d s)=Fin.cons (‖d‖⁻¹ • d) (unitWindow s) :=
    krylov.Methods.unitWindow_cons d s
  rw [he]
  intro i
  refine Fin.cases ?_ (fun a=>?_) i
  · intro j
    refine Fin.cases ?_ (fun b=>?_) j
    · intro hh
      exact False.elim (hh rfl)
    · intro _hh
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [real_inner_comm]
      exact hp b
  · intro j
    refine Fin.cases ?_ (fun b=>?_) j
    · intro _hh
      simpa only [Fin.cons_zero,Fin.cons_succ] using hp a
    · intro hh
      simpa only [Fin.cons_succ] using hangle a b (fun hab=>hh (congrArg Fin.succ hab))

end
end krylov.Convergence
