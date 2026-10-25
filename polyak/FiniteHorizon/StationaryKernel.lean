import polyak.FiniteHorizon.StationaryBanded
import polyak.Energy.FiniteCombination

/-!
Article: Appendix C, the concrete quadratic kernel of an arbitrary window price.
Use: its actual finite-position coefficients give the same half-circle symbol
as stationary evaluation, and its sampled values have exactly the C charge.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral
open scoped BigOperators

def priceQuadraticKernel {H : ℕ} (L : WindowPrice H) (t : ℝ) : Kernel :=
  (Finset.univ.toList.flatMap fun a : Fin (H+2) =>
    Finset.univ.toList.map fun b : Fin (H+2) =>
      (priceQuadraticCoefficients L t a b,((a : ℤ),(b : ℤ))))

theorem kernelEval_priceQuadratic {H : ℕ} (L : WindowPrice H) (t : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (k : ℤ) :
    kernelEval (priceQuadraticKernel L t) f k=
      ∑ a : Fin (H+2),∑ b : Fin (H+2),priceQuadraticCoefficients L t a b*
        inner ℝ (f (k+(a : ℤ))) (f (k+(b : ℤ))) := by
  simp only [priceQuadraticKernel,kernelEval_flatMap,Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro a _
  simp [kernelEval,List.map_map,Finset.sum_map_toList]

theorem character_re_coe (n : ℤ) (ω : ℝ) :
    (character n (ω : FrequencyCircle)).re=Real.cos ((n : ℝ)*ω) := by
  rw [character_coe,Complex.exp_re]
  simp

theorem kernelSymbol_priceQuadratic {H : ℕ} (L : WindowPrice H) (t : ℝ) (c : Frequency) :
    kernelSymbol (priceQuadraticKernel L t) (Real.arccos c : FrequencyCircle)=
      priceCosineSymbol L t c := by
  rw [kernelSymbol_eq_eval,kernelEval_priceQuadratic]
  simp_rw [inner_character,character_re_coe]
  change (∑ a : Fin (H+2),∑ b : Fin (H+2),priceQuadraticCoefficients L t a b*
    Real.cos (((0+(b : ℤ)-(0+(a : ℤ)) : ℤ) : ℝ)*Real.arccos c))=_
  unfold priceCosineSymbol
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : ((0+(b : ℤ)-(0+(a : ℤ)) : ℤ) : ℝ)=-((a.val : ℝ)-(b.val : ℝ)):=by
    push_cast
    ring
  rw [he,neg_mul,Real.cos_neg]

def priceValueLagCoefficient {H : ℕ} (L : WindowPrice H) (t : ℝ) (n : ℕ) : ℝ :=
  if hn : n∈Finset.Icc 1 H then priceValueCoefficients L t ⟨n-1,by
    have := Finset.mem_Icc.mp hn
    omega⟩ else 0

theorem sum_priceValueLagCoefficient {H : ℕ} (L : WindowPrice H) (t : ℝ)
    (h : ℕ → ℝ) (k : ℕ) :
    (∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n*h (k+n))=
      ∑ i : Fin H,priceValueCoefficients L t i*h (k+i.val+1) := by
  apply Finset.sum_bij (fun n hn => (⟨n-1,by have := Finset.mem_Icc.mp hn; omega⟩ : Fin H))
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn m hm he
    have hn':=(Finset.mem_Icc.mp hn).1
    have hm':=(Finset.mem_Icc.mp hm).1
    have he':=congrArg Fin.val he
    change n-1=m-1 at he'
    omega
  · intro i _
    refine ⟨i.val+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fin.ext
    simp
  · intro n hn
    simp only [priceValueLagCoefficient,dite_eq_left hn]
    congr 2
    have hn':=(Finset.mem_Icc.mp hn).1
    omega

theorem sum_priceValueLagCoefficient_const {H : ℕ} (L : WindowPrice H) (t : ℝ) :
    (∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n)=priceValueCharge L t := by
  simpa only [mul_one,priceValueCharge] using sum_priceValueLagCoefficient L t (fun _ => 1) 0

theorem sum_priceValueLagCoefficient_Icc_zero {H : ℕ} (L : WindowPrice H) (t : ℝ)
    (f : ℕ → ℝ) :
    (∑ n∈Finset.Icc 0 H,priceValueLagCoefficient L t n*f n)=
      ∑ i : Fin H,priceValueCoefficients L t i*f (i.val+1) := by
  have hsub : Finset.Icc 1 H⊆Finset.Icc 0 H:=by intro n hn; have := Finset.mem_Icc.mp hn; simp only [Finset.mem_Icc]; omega
  have he : (∑ n∈Finset.Icc 0 H,priceValueLagCoefficient L t n*f n)=
      ∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n*f n := by
    symm
    apply Finset.sum_subset hsub
    intro n _ hn
    simp only [priceValueLagCoefficient,dite_eq_right hn,zero_mul]
  rw [he]
  simpa only [Nat.zero_add] using sum_priceValueLagCoefficient L t f 0

theorem integerDiscount_nat_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → E) (t : ℝ) (k : ℤ) (hk : 0≤k) :
    discountedInteger x t k=integerDiscount (fun z => x z.toNat) t k := by
  have he : (k.toNat : ℤ)=k:=by omega
  have he' : (k.toNat : ℝ)=(k : ℝ):=by exact_mod_cast he
  simp only [discountedInteger,discountedPosition,integerDiscount,he',neg_mul]

theorem integerDiscountValue_nat_nonneg (v : ℕ → ℝ) (t : ℝ) (k : ℤ) (hk : 0≤k) :
    discountedValue v t k.toNat=integerDiscountValue (fun z => v z.toNat) t k := by
  have he : (k.toNat : ℤ)=k:=by omega
  have he' : (k.toNat : ℝ)=(k : ℝ):=by exact_mod_cast he
  simp only [discountedValue,integerDiscountValue,he']

theorem integerWindow_hRun_nat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    integerWindow H (fun z => r.x z.toNat) (fun z => sampleValue r z.toNat) k=
      segmentWindow (r.segment k) k := by
  apply Prod.ext
  · ext i j
    have hi : ((k : ℤ)-(H : ℤ)+(i : ℤ)).toNat=k-H+i:=by omega
    have hj : ((k : ℤ)-(H : ℤ)+(j : ℤ)).toNat=k-H+j:=by omega
    change inner ℝ (r.x _) (r.x _)=inner ℝ (r.x _) (r.x _)
    rw [hi,hj]
  · ext i
    have hi : ((k : ℤ)-(H : ℤ)+(i : ℤ)+1).toNat=k-H+(i+1):=by omega
    change sampleValue r _=r.value (k-H+(i+1))
    rw [hi,sampleValue_eq r (by omega)]

theorem hRun_priceBandedEval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (L : WindowPrice H)
    (t : ℝ) (k : ℕ) :
    kernelEval (priceQuadraticKernel L t) (discountedInteger r.x t) k+
      (∑ n∈Finset.Icc 1 H,priceValueLagCoefficient L t n*discountedValue (sampleValue r) t (k+n))=
      Real.exp (-2*(k : ℝ)*t)*L (segmentWindow (r.segment (k+H)) (k+H)) := by
  have he:=priceBandedEval_discounted L t (fun z => r.x z.toNat)
    (fun z => sampleValue r z.toNat) (k : ℤ)
  have hc : (k : ℤ)+(H : ℤ)=((k+H : ℕ) : ℤ):=by omega
  rw [hc,integerWindow_hRun_nat r (k+H) (by omega)] at he
  simp only [Int.cast_natCast] at he
  rw [←he,kernelEval_priceQuadratic,sum_priceValueLagCoefficient]
  unfold priceBandedEval
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [integerDiscount_nat_nonneg r.x t _ (by omega),integerDiscount_nat_nonneg r.x t _ (by omega)]
end polyak.FiniteHorizon
