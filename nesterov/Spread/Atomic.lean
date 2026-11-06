import nesterov.Spread.FiniteConvex
import nesterov.Spread.Tail
import nesterov.Spectral.Finite

/-! Strict feasible spectra with the half-step envelope have finite feasible
spectra on exactly the same band. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral Set
open scoped BigOperators NNReal

theorem exists_finite_of_strict (a : SymbolPair) {t η : ℝ} (ht : t<0)
    (hη : 0<η) (hη1 : η<1) (ν : Spectrum) (S : Set Frequency)
    (hS : ∀ᵐ c ∂(ν:Measure Frequency),c∈S)
    (hg : ∀ c∈S,0<g a c)
    (hosc : ∀ c∈S,∀ n : ℕ,
      lowerOsc a n c≤4*g a c ∧ upperOsc a n c≤4*g a c)
    (hmean : 0<meanG ν a)
    (hslack : ∀ n : ℕ,1≤n →
      0<lowerSlack a t ν (-(1-η)*meanG ν a) n ∧
      0<upperSlack a t ν (-(1-η)*meanG ν a) n) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (c : J→Frequency)
      (hw : ∑ j,w j=1), (∀ j,c j∈S) ∧
      ∃ C : ℝ,Feasible a t (finiteSpectrum w c hw) C ∧
        |C|<meanG (finiteSpectrum w c hw) a := by
  classical
  obtain ⟨N,hN⟩ := exists_uniform_tail ht hη hη1
  let f : Frequency→Option (Bool×Fin N)→ℝ := fun c i=>
    match i with
    | none => g a c
    | some (b,k) => if b then lowerPoint a t η (k.val+1) c else upperPoint a t η (k.val+1) c
  have hcont (i : Option (Bool×Fin N)) : Continuous (fun c=>f c i) := by
    rcases i with _|⟨b,k⟩
    · exact continuous_g a
    · cases b
      · exact continuous_upperPoint a t η _
      · exact continuous_lowerPoint a t η _
  have hpos (i : Option (Bool×Fin N)) : 0<∫ c,f c i ∂ν := by
    rcases i with _|⟨b,k⟩
    · exact hmean
    · cases b
      · exact (upperSlack_eq_integral a t η ν (k.val+1)) ▸ (hslack (k.val+1) (by omega)).2
      · exact (lowerSlack_eq_integral a t η ν (k.val+1)) ▸ (hslack (k.val+1) (by omega)).1
  obtain ⟨J,hJ,w,c,hw,hs,hc,hf⟩ := finite_strict_moments_on (ν:Measure Frequency) f S hS
    (fun i=>polyak.Spectral.integrable_continuous ν (hcont i)) hpos
  let w' : J→ℝ≥0 := fun j=>⟨w j,hw j⟩
  have hs' : ∑ j,w' j=1 := by
    apply NNReal.eq
    simp only [NNReal.coe_sum,NNReal.coe_one]
    change (∑ j,w j)=1
    exact hs
  let ν' := finiteSpectrum w' c hs'
  have hG : meanG ν' a=∑ j,w j*g a (c j) := by
    change (∫ z,g a z ∂polyak.Waves.finiteSpectrum w' c hs')=_
    rw [polyak.Waves.finiteSpectrum_integral]
    rfl
  have hGp : 0<meanG ν' a := by
    rw [hG]
    exact hf none
  let C : ℝ := -(1-η)*meanG ν' a
  have hC : |C|<meanG ν' a := extreme_charge_reserve hη hη1 hGp
  have hlo (n : ℕ) : lowerSlack a t ν' C n=∑ j,w j*lowerPoint a t η n (c j) := by
    rw [show C= -(1-η)*meanG ν' a from rfl,lowerSlack_eq_integral]
    change (∫ z,lowerPoint a t η n z ∂polyak.Waves.finiteSpectrum w' c hs')=_
    rw [polyak.Waves.finiteSpectrum_integral]
    rfl
  have hup (n : ℕ) : upperSlack a t ν' C n=∑ j,w j*upperPoint a t η n (c j) := by
    rw [show C= -(1-η)*meanG ν' a from rfl,upperSlack_eq_integral]
    change (∫ z,upperPoint a t η n z ∂polyak.Waves.finiteSpectrum w' c hs')=_
    rw [polyak.Waves.finiteSpectrum_integral]
    rfl
  have hwpos : ∃ j,0<w j := by
    by_contra! hn
    have hz (j : J) : w j=0 := le_antisymm (hn j) (hw j)
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  have htail (n : ℕ) (hn : N≤n) : 0<lowerSlack a t ν' C n ∧ 0<upperSlack a t ν' C n := by
    obtain ⟨j,hj⟩ := hwpos
    obtain ⟨hm,hp⟩ := hN n hn
    have hpoints (j : J) := points_positive_of_tail a ht hm hp (c j)
      (hg _ (hc j)) (hosc _ (hc j) n).1 (hosc _ (hc j) n).2
    rw [hlo,hup]
    constructor
    · exact Finset.sum_pos' (fun j _=>mul_nonneg (hw j) (hpoints j).1.le)
        ⟨j,Finset.mem_univ _,mul_pos hj (hpoints j).1⟩
    · exact Finset.sum_pos' (fun j _=>mul_nonneg (hw j) (hpoints j).2.le)
        ⟨j,Finset.mem_univ _,mul_pos hj (hpoints j).2⟩
  refine ⟨J,hJ,w',c,hs',hc,C,⟨hC.le,?_⟩,hC⟩
  intro n hn
  by_cases hlarge : N≤n
  · exact ⟨(htail n hlarge).1.le,(htail n hlarge).2.le⟩
  · let k : Fin N := ⟨n-1,by omega⟩
    have hk : k.val+1=n := by dsimp [k];omega
    have hl := hf (some (true,k))
    have hu := hf (some (false,k))
    change 0<∑ j,w j*lowerPoint a t η (k.val+1) (c j) at hl
    change 0<∑ j,w j*upperPoint a t η (k.val+1) (c j) at hu
    rw [hk,←hlo] at hl
    rw [hk,←hup] at hu
    exact ⟨hl.le,hu.le⟩

end
end nesterov.Spread
