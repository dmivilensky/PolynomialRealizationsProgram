import polyak.FiniteHorizon.Banded
import polyak.Energy.Symbol

/-!
Article: Appendix C, the actual finite interpolation kernel in a width-seven window.
Use: shifts −1,…,6 become coordinates 0,…,7. The conversion preserves both
the Hilbert quadratic form and its frequency symbol, with no coefficient assumption.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy
open scoped BigOperators

def shiftIndex7 (z : ℤ) : Fin 8 := ⟨(z+1).toNat%8,Nat.mod_lt _ (by norm_num)⟩

theorem shiftIndex7_cast {z : ℤ} (hz : -1≤z ∧ z≤6) : (shiftIndex7 z : ℤ)=z+1 := by
  change (((z+1).toNat%8 : ℕ) : ℤ)=z+1
  rw [Nat.mod_eq_of_lt (by omega : (z+1).toNat<8)]
  omega

def singleKernelMatrix7 (p : ℝ×(ℤ×ℤ)) : WindowMatrix7 :=
  fun a b => if a=shiftIndex7 p.2.1 ∧ b=shiftIndex7 p.2.2 then p.1 else 0

def kernelMatrix7 : Kernel → WindowMatrix7
  | [] => 0
  | p::K => fun a b => singleKernelMatrix7 p a b+kernelMatrix7 K a b

theorem singleKernelMatrix7_eval (p : ℝ×(ℤ×ℤ))
    (h₁ : -1≤p.2.1 ∧ p.2.1≤6) (h₂ : -1≤p.2.2 ∧ p.2.2≤6)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (j : ℤ) :
    matrixEval7 (singleKernelMatrix7 p) f (j-1)=
      p.1*inner ℝ (f (j+p.2.1)) (f (j+p.2.2)) := by
  simp only [matrixEval7,singleKernelMatrix7,ite_and,ite_mul,zero_mul,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,
    ↓reduceIte]
  rw [shiftIndex7_cast h₁,shiftIndex7_cast h₂]
  congr 2 <;> congr 1 <;> ring

theorem singleKernelMatrix7_symbol (p : ℝ×(ℤ×ℤ))
    (h₁ : -1≤p.2.1 ∧ p.2.1≤6) (h₂ : -1≤p.2.2 ∧ p.2.2≤6)
    (θ : FrequencyCircle) :
    coefficientSymbol (singleKernelMatrix7 p) θ=p.1*(character (p.2.2-p.2.1) θ).re := by
  simp only [coefficientSymbol,singleKernelMatrix7,ite_and,ite_mul,zero_mul,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,
    ↓reduceIte]
  rw [shiftIndex7_cast h₁,shiftIndex7_cast h₂]
  rw [show p.2.1+1-(p.2.2+1)=p.2.1-p.2.2 by ring]
  rw [character_sub_re,character_sub_re]
  ring

theorem singleKernelMatrix7_mass (p : ℝ×(ℤ×ℤ)) :
    matrixMass7 (singleKernelMatrix7 p)=|p.1| := by
  unfold matrixMass7 singleKernelMatrix7
  have he (a b : Fin 8) :
      |if a=shiftIndex7 p.2.1 ∧ b=shiftIndex7 p.2.2 then p.1 else 0|=
      if a=shiftIndex7 p.2.1 ∧ b=shiftIndex7 p.2.2 then |p.1| else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp [ite_and]

theorem kernelMatrix7_eval (K : Kernel)
    (hs : ∀ p∈K,(-1≤p.2.1 ∧ p.2.1≤6) ∧ (-1≤p.2.2 ∧ p.2.2≤6))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (j : ℤ) : matrixEval7 (kernelMatrix7 K) f (j-1)=kernelEval K f j := by
  induction K with
  | nil => simp [kernelMatrix7,matrixEval7,kernelEval]
  | cons p K ih =>
    rw [kernelMatrix7,matrixEval7_add,singleKernelMatrix7_eval p
      (hs p List.mem_cons_self).1 (hs p List.mem_cons_self).2,
      ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))]
    rfl

theorem kernelMatrix7_symbol (K : Kernel)
    (hs : ∀ p∈K,(-1≤p.2.1 ∧ p.2.1≤6) ∧ (-1≤p.2.2 ∧ p.2.2≤6))
    (θ : FrequencyCircle) : coefficientSymbol (kernelMatrix7 K) θ=kernelSymbol K θ := by
  induction K with
  | nil => simp [kernelMatrix7,coefficientSymbol,kernelSymbol]
  | cons p K ih =>
    rw [kernelMatrix7,coefficientSymbol_add7,singleKernelMatrix7_symbol p
      (hs p List.mem_cons_self).1 (hs p List.mem_cons_self).2,
      ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))]
    rfl

theorem kernelMatrix7_mass_le (K : Kernel) : matrixMass7 (kernelMatrix7 K)≤kernelSize K := by
  induction K with
  | nil => simp [kernelMatrix7,matrixMass7,kernelSize]
  | cons p K ih =>
    have h := matrixMass7_add_le (singleKernelMatrix7 p) (kernelMatrix7 K)
    rw [singleKernelMatrix7_mass] at h
    exact h.trans (by
      change |p.1|+matrixMass7 (kernelMatrix7 K)≤|p.1|+kernelSize K
      exact add_le_add le_rfl ih)

end polyak.FiniteHorizon
