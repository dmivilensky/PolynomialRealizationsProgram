import polyak.Duality.FiniteAlternative

/-!
Article: Appendix C, separation on the zero set of an affine stationary price.
Use: the price may contain the unrestricted value constant C. Two additional
opposite inequalities represent its equality; their nonnegative multipliers
combine into the unrestricted real equality multiplier.
-/
noncomputable section
namespace polyak.Duality
open MeasureTheory Spectral
open scoped BigOperators

theorem finite_strict_alternative_affine_equality {I : Type*} [Fintype I]
    (φ : I → C(Frequency,ℝ)) (σ : I → ℝ) (p : I) (hp : 0<σ p)
    (e : C(Frequency,ℝ)) (e₀ : ℝ)
    (hinfeasible : ¬ ∃ (ν : Spectrum) (C : ℝ),
      (∀ i,0≤(∫ c,φ i c ∂ν)+σ i*C) ∧ (∫ c,e c ∂ν)+e₀*C=0) :
    ∃ (w : I → ℝ) (ζ ε : ℝ), (∀ i,0≤w i) ∧ 0<ε ∧
      (∑ i,w i*σ i)+ζ*e₀=0 ∧
      ∀ c,(∑ i,w i*φ i c)+ζ*e c≤ -ε := by
  classical
  let φ' : I ⊕ Bool → C(Frequency,ℝ) := Sum.elim φ (fun b => if b then -e else e)
  let σ' : I ⊕ Bool → ℝ := Sum.elim σ (fun b => if b then -e₀ else e₀)
  have hi : ¬ ∃ (ν : Spectrum) (C : ℝ),
      ∀ i,0≤(∫ c,φ' i c ∂ν)+σ' i*C := by
    rintro ⟨ν,C,h⟩
    apply hinfeasible
    refine ⟨ν,C,fun i => h (.inl i),?_⟩
    have hlo := h (.inr false)
    have hhi := h (.inr true)
    simp only [φ',σ',Sum.elim_inr,Bool.false_eq_true,↓reduceIte] at hlo
    simp only [φ',σ',Sum.elim_inr,↓reduceIte,ContinuousMap.neg_apply,integral_neg] at hhi
    linarith
  obtain ⟨w,ε,hw,hε,hcancel,hstrict⟩ := finite_strict_alternative φ' σ' (.inl p)
    (by simpa only [σ',Sum.elim_inl] using hp) hi
  refine ⟨fun i => w (.inl i),w (.inr false)-w (.inr true),ε,
    fun i => hw (.inl i),hε,?_,?_⟩
  · simp only [Fintype.sum_sum_type,Fintype.sum_bool,σ',Sum.elim_inl,Sum.elim_inr,
      Bool.false_eq_true,↓reduceIte] at hcancel
    linarith
  · intro c
    have hs := hstrict c
    simp only [Fintype.sum_sum_type,Fintype.sum_bool,φ',Sum.elim_inl,Sum.elim_inr,
      Bool.false_eq_true,↓reduceIte,ContinuousMap.neg_apply] at hs
    linarith

end polyak.Duality
