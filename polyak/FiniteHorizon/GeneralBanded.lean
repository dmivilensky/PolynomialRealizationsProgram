import polyak.FiniteHorizon.ClassBanded
import polyak.FiniteHorizon.FactorizationGram

/-!
Article: Appendix C, the literal arbitrary-width/offset form in Lemma plateauclass.
Use: a dense finite real matrix and value coefficients are converted exactly
to the general finite kernel theorem. No bound on the degree is imposed.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Filter Set Finset
open scoped Topology

def coefficientKernel {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ) : Kernel:=
  (List.ofFn fun a : Fin (D+1) => a).flatMap fun a =>
    List.ofFn fun b : Fin (D+1) => (C a b,((a : ℤ),(b : ℤ)))

theorem coefficientKernel_eval {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) :
    kernelEval (coefficientKernel C) f j=
      ∑ a,∑ b,C a b*inner ℝ (f (j+(a : ℤ))) (f (j+(b : ℤ))) := by
  unfold coefficientKernel
  rw [kernelEval_flatMap,List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro a _
  simp only [kernelEval,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem coefficientKernel_symbol {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ)
    (θ : FrequencyCircle) : kernelSymbol (coefficientKernel C) θ=coefficientSymbol C θ := by
  unfold coefficientKernel
  rw [kernelSymbol_flatMap,List.map_ofFn,List.sum_ofFn]
  unfold coefficientSymbol
  apply sum_congr rfl
  intro a _
  simp only [kernelSymbol,List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro b _
  change C a b*(character ((b : ℤ)-(a : ℤ)) θ).re=
    C a b*(character ((a : ℤ)-(b : ℤ)) θ).re
  rw [show (b : ℤ)-(a : ℤ)= -((a : ℤ)-(b : ℤ)) by ring,fourier_neg,Complex.conj_re]

/-- The character definition is exactly the article's real cosine polynomial. -/
theorem coefficientSymbol_coe {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ) (ω : ℝ) :
    coefficientSymbol C (ω : FrequencyCircle)=
      ∑ a,∑ b,C a b*Real.cos (((a : ℝ)-(b : ℝ))*ω) := by
  have hc (n : ℤ) : (character n (ω : FrequencyCircle)).re=Real.cos ((n : ℝ)*ω):=by
    rw [character_coe,Complex.exp_re]
    simp
  unfold coefficientSymbol
  simp_rw [hc,Int.cast_sub,Int.cast_natCast]

def natValueCoefficient {D : ℕ} (d : Fin (D+1) → ℝ) (k : ℕ) : ℝ:=
  if hk : k<D+1 then d ⟨k,hk⟩ else 0

theorem natValueCoefficient_charge {D : ℕ} (d : Fin (D+1) → ℝ) :
    (∑ k∈range (D+1),natValueCoefficient d k)=∑ a,d a := by
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [natValueCoefficient,Fin.is_lt,↓reduceDIte,Fin.eta]

theorem natValueCoefficient_eval {D : ℕ} (d : Fin (D+1) → ℝ) (h : ℕ → ℝ) (k : ℕ) :
    finiteValueCombination (range (D+1)) (natValueCoefficient d) h k=
      ∑ a,d a*h (k+a) := by
  unfold finiteValueCombination
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [natValueCoefficient,Fin.is_lt,↓reduceDIte,Fin.eta]

def bandedEval {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ) (d : Fin (D+1) → ℝ)
    (o : ℤ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ:=
  (∑ a,∑ b,C a b*inner ℝ (f (j+o+(a : ℤ))) (f (j+o+(b : ℤ))))+
    ∑ a,d a*h (j+o+(a : ℤ))

theorem bandedEval_at_nat {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ) (d : Fin (D+1) → ℝ)
    (o : ℤ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℕ → ℝ) (k : ℕ) :
    bandedEval C d o f (fun l => h l.toNat) ((k : ℤ)-o)=
      kernelEval (coefficientKernel C) f k+
        finiteValueCombination (range (D+1)) (natValueCoefficient d) h k := by
  rw [bandedEval,sub_add_cancel,coefficientKernel_eval,natValueCoefficient_eval]
  congr 1

/-- Lemma plateauclass in the article's original dense-matrix form, for every
finite width D and every integer offset o. Symmetry is unnecessary for the result. -/
theorem not_general_banded_at_rate {A B β r : ℝ} {H : ℕ} (G : SegmentClass A B β H)
    (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r))
    (D : ℕ) (C : Fin (D+1) → Fin (D+1) → ℝ) (d : Fin (D+1) → ℝ) (o : ℤ)
    (hcharge : ∑ a,d a=0)
    (hstrict : ∀ ω : ℝ,0≤ω → ω≤Real.pi → coefficientSymbol C (ω : FrequencyCircle)<0)
    (hsource : ∀ dimension n : ℕ,
      ∀ s : HSegment (EuclideanSpace ℝ (Fin dimension)) A B β H n,G.contains dimension n s →
        ∀ j : ℤ,1≤j+o → j+o+(D : ℤ)≤n →
          0≤bandedEval C d o (discountedInteger s.x (Real.log r))
            (fun l => segmentDiscountedValue s (Real.log r) l.toNat) j) : False := by
  apply G.not_banded_at_rate hpos hr hlim (coefficientKernel C) (range (D+1))
    (natValueCoefficient d) (by rw [natValueCoefficient_charge,hcharge])
    (fun ω hlo hhi => by rw [coefficientKernel_symbol]; exact hstrict ω hlo hhi) (D+1)
  intro dimension n s hs k hk hkn
  have hh:=hsource dimension n s hs ((k : ℤ)-o) (by omega) (by omega)
  rwa [bandedEval_at_nat] at hh

end polyak.FiniteHorizon
