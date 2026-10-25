import polyak.FiniteHorizon.Factorization
import Mathlib.Algebra.BigOperators.Fin

/-!
Article: Appendix C, finite coefficient vectors and the Parseval trace bound.
Use: the constructive real filters become a finite positive semidefinite Gram
matrix on exactly D+1 causal coordinates; its trace is the mean symbol.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy MeasureTheory
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨Real.two_pi_pos⟩

/-- Coalesce every repeated shift before extracting the finite coefficient vector. -/
def filterCoefficient (L : LinearFilter) (a : ℤ) : ℝ :=
  (L.map fun p => if p.2=a then p.1 else 0).sum

theorem filterCoefficient_cons (p : ℝ×ℤ) (L : LinearFilter) (a : ℤ) :
    filterCoefficient (p::L) a=(if p.2=a then p.1 else 0)+filterCoefficient L a := by
  simp [filterCoefficient]

/-- A causal supported filter is exactly its D+1 coalesced coefficients. -/
theorem filterFourier_eq_sum {D : ℕ} {L : LinearFilter} (hL : FilterWithin D L)
    (θ : FrequencyCircle) :
    filterFourier L θ=
      ∑ a : Fin (D+1), (filterCoefficient L a : ℂ)*character a θ := by
  classical
  induction L with
  | nil => simp [filterFourier,filterCoefficient]
  | cons p L ih =>
    have hp:=hL p (by simp)
    have hL' : FilterWithin D L:=fun q hq => hL q (by simp [hq])
    let a : Fin (D+1):=⟨p.2.toNat,by omega⟩
    have hpa : (a : ℤ)=p.2:=by dsimp [a]; exact Int.toNat_of_nonneg hp.1
    have heq (b : Fin (D+1)) : p.2=(b : ℤ) ↔ b=a := by
      constructor
      · intro hb
        apply Fin.ext
        change (b : ℕ)=p.2.toNat
        omega
      · intro hb
        subst b
        exact hpa.symm
    have hsingle :
        (∑ b : Fin (D+1), (((if p.2=(b : ℤ) then p.1 else 0) : ℝ) : ℂ)*
          character b θ)=(p.1 : ℂ)*character p.2 θ := by
      rw [Finset.sum_eq_single a]
      · simp [hpa]
      · intro b _ hba
        have hb : p.2≠(b : ℤ):=fun he => hba ((heq b).mp he)
        simp only [ite_eq_right hb,Complex.ofReal_zero,zero_mul]
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    change (p.1 : ℂ)*character p.2 θ+filterFourier L θ=_
    rw [ih hL']
    simp_rw [filterCoefficient_cons,Complex.ofReal_add,add_mul]
    rw [Finset.sum_add_distrib,hsingle]

/-- The Gram symbol of real coefficients is the squared complex Fourier value. -/
theorem coefficientGram_eq_normSq {D : ℕ} (f : Fin (D+1) → ℝ) (θ : FrequencyCircle) :
    fourierGram (fun a : Fin (D+1) => (a : ℤ)) f θ=
      Complex.normSq (∑ a : Fin (D+1), (f a : ℂ)*character a θ) := by
  rw [fourierGram_eq_sq]
  simp only [smul_eq_mul,Real.norm_eq_abs,sq_abs,Complex.normSq_apply,
    Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp_rw [mul_comm]
  ring_nf

theorem coefficientGram_scale {D : ℕ} (r : ℝ) (f : Fin (D+1) → ℝ)
    (θ : FrequencyCircle) :
    fourierGram (fun a : Fin (D+1) => (a : ℤ)) (fun a => r*f a) θ=
      r^2*fourierGram (fun a : Fin (D+1) => (a : ℤ)) f θ := by
  unfold fourierGram
  have hinner (a b : Fin (D+1)) :
      inner ℝ (r*f a) (r*f b)=r^2*inner ℝ (f a) (f b) := by
    change inner ℝ (r • f a) (r • f b)=_
    rw [real_inner_smul_left,real_inner_smul_right]
    ring
  simp_rw [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact conversion of a supported real filter to a finite Gram symbol. -/
theorem filterSquare_eq_coefficientGram {D : ℕ} {L : LinearFilter}
    (hL : FilterWithin D L) (θ : FrequencyCircle) :
    filterSquare L θ=fourierGram (fun a : Fin (D+1) => (a : ℤ))
      (fun a => filterCoefficient L a) θ := by
  rw [filterSquare_eq_normSq,coefficientGram_eq_normSq,filterFourier_eq_sum hL]

/-- Finite real coefficient vectors, in the form required by local Gram telescoping. -/
structure GramFactors (D : ℕ) (F : FrequencyCircle → ℝ) where
  count : ℕ
  coefficient : Fin count → Fin (D+1) → ℝ
  exact : ∀ θ, F θ=∑ j, fourierGram (fun a : Fin (D+1) => (a : ℤ)) (coefficient j) θ

/-- Remove nonnegative weights by their real square roots and coalesce all shifts. -/
def SquareFactorization.toGram {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : SquareFactorization D F) : GramFactors D F where
  count:=cert.terms.length
  coefficient j a:=Real.sqrt cert.terms[j].1*filterCoefficient cert.terms[j].2 a
  exact θ:=by
    rw [cert.exact]
    have hsum : weightedSquares cert.terms θ=
        ∑ j : Fin cert.terms.length, cert.terms[j].1*filterSquare cert.terms[j].2 θ := by
      unfold weightedSquares
      rw [← List.ofFn_getElem_eq_map cert.terms
        (fun term : ℝ×LinearFilter => term.1*filterSquare term.2 θ)]
      exact List.sum_ofFn
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : cert.terms[j]∈cert.terms:=List.getElem_mem _
    rw [coefficientGram_scale,Real.sq_sqrt (cert.weight_nonneg _ hj),
      ←filterSquare_eq_coefficientGram (cert.within _ hj)]

/-- Trace of the finite positive semidefinite coefficient matrix. -/
def GramFactors.trace {D : ℕ} {F : FrequencyCircle → ℝ} (cert : GramFactors D F) : ℝ :=
  ∑ j, ∑ a, (cert.coefficient j a)^2

theorem GramFactors.trace_nonneg {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) : 0≤cert.trace := by
  unfold GramFactors.trace
  positivity

/-- Parseval identifies the exact coefficient trace, independently of the number of filters. -/
theorem GramFactors.trace_eq_integral {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) :
    cert.trace=∫ θ : FrequencyCircle,F θ ∂AddCircle.haarAddCircle := by
  have hF : F=(fun θ => ∑ j, fourierGram (fun a : Fin (D+1) => (a : ℤ))
      (cert.coefficient j) θ):=funext cert.exact
  conv_rhs => rw [hF]
  rw [integral_finsetSum]
  · unfold GramFactors.trace
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_fourierGram_of_injective]
    · simp only [Real.norm_eq_abs,sq_abs]
    · intro a b hab
      apply Fin.ext
      change (a : ℤ)=(b : ℤ) at hab
      exact_mod_cast hab
  · intro j _
    exact (continuous_fourierGram _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The actual positive semidefinite Gram coefficients. -/
def GramFactors.matrix {D : ℕ} {F : FrequencyCircle → ℝ} (cert : GramFactors D F)
    (a b : Fin (D+1)) : ℝ := ∑ j, cert.coefficient j a*cert.coefficient j b

/-- Absolute coefficient mass costs only the width, never the number of squared filters. -/
theorem GramFactors.matrix_mass_le {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) :
    (∑ a, ∑ b, |cert.matrix a b|)≤(D+1 : ℕ)*cert.trace := by
  classical
  have hab (a b : Fin (D+1)) :
      |cert.matrix a b|≤∑ j,((cert.coefficient j a)^2+(cert.coefficient j b)^2)/2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (cert.coefficient j a-cert.coefficient j b),
      sq_nonneg (cert.coefficient j a+cert.coefficient j b)]
  calc
    _ ≤ ∑ a, ∑ b, ∑ j,((cert.coefficient j a)^2+(cert.coefficient j b)^2)/2 := by
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hab a b
    _ = _ := by
      unfold GramFactors.trace
      conv_lhs =>
        arg 2
        ext a
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp_rw [add_div,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←Finset.mul_sum,←Finset.sum_div]
      ring

/-- The exact dense real coefficient symbol of a causal quadratic window. -/
def coefficientSymbol {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ)
    (θ : FrequencyCircle) : ℝ :=
  ∑ a, ∑ b, C a b*(character ((a : ℤ)-(b : ℤ)) θ).re

theorem GramFactors.matrix_symmetric {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (a b : Fin (D+1)) : cert.matrix a b=cert.matrix b a := by
  unfold GramFactors.matrix
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coefficient matrix has the original factored symbol, with the exact
sign convention used for the original dense quadratic matrix. -/
theorem GramFactors.matrix_symbol {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (θ : FrequencyCircle) :
    coefficientSymbol cert.matrix θ=F θ := by
  rw [cert.exact]
  unfold coefficientSymbol GramFactors.matrix fourierGram
  simp_rw [Real.inner_apply,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show (a : ℤ)-(b : ℤ)= -((b : ℤ)-(a : ℤ)) by ring,fourier_neg]
  rfl

/-- The very same matrix represents a finite sum of squared filters in every
real Hilbert space, not merely on complex Fourier waves. -/
theorem GramFactors.matrix_eval {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin (D+1) → E) :
    (∑ a, ∑ b, cert.matrix a b*inner ℝ (f a) (f b))=
      ∑ j, ‖∑ a, cert.coefficient j a • f a‖^2 := by
  unfold GramFactors.matrix
  simp_rw [Finset.sum_mul,←real_inner_self_eq_norm_sq,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

@[fun_prop] theorem continuous_coefficientSymbol {D : ℕ}
    (C : Fin (D+1) → Fin (D+1) → ℝ) : Continuous (coefficientSymbol C) := by
  unfold coefficientSymbol
  fun_prop

/-- Parseval selects precisely the diagonal coefficients, with normalized Haar measure. -/
theorem integral_coefficientSymbol {D : ℕ} (C : Fin (D+1) → Fin (D+1) → ℝ) :
    (∫ θ : FrequencyCircle, coefficientSymbol C θ ∂AddCircle.haarAddCircle)=
      ∑ a, C a a := by
  classical
  unfold coefficientSymbol
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul,integral_character_re]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hba
        have he : (a : ℤ)-(b : ℤ)≠0:=by
          intro h
          apply hba
          apply Fin.ext
          have hab : (a : ℤ)=(b : ℤ):=sub_eq_zero.mp h
          exact_mod_cast hab.symm
        simp only [ite_eq_right he,mul_zero]
      · intro h
        exact (h (Finset.mem_univ a)).elim
    · intro b _
      exact ((Complex.continuous_re.comp (character ((a : ℤ)-(b : ℤ))).continuous).const_mul
        (C a b)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro a _
    exact (by fun_prop : Continuous (fun θ : FrequencyCircle =>
      ∑ b, C a b*(character ((a : ℤ)-(b : ℤ)) θ).re)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The chosen factors have the exact trace required in Lemma telescoping. -/
theorem GramFactors.trace_eq_neg_diagonal {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (C : Fin (D+1) → Fin (D+1) → ℝ) (ε : ℝ)
    (hF : ∀ θ, F θ= -coefficientSymbol C θ-ε) :
    cert.trace= -(∑ a, C a a)-ε := by
  rw [cert.trace_eq_integral]
  have he : F=(fun θ => -coefficientSymbol C θ-ε):=funext hF
  rw [he,integral_sub]
  · rw [integral_neg,integral_coefficientSymbol]
    simp
  · exact (continuous_coefficientSymbol C).neg.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact integrable_const _

/-- The coefficient trace is bounded uniformly by the original quadratic coefficient size. -/
theorem GramFactors.trace_le_matrix_mass {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (C : Fin (D+1) → Fin (D+1) → ℝ) {ε : ℝ}
    (hε : 0≤ε) (hF : ∀ θ, F θ= -coefficientSymbol C θ-ε) :
    cert.trace≤∑ a, ∑ b, |C a b| := by
  classical
  rw [cert.trace_eq_neg_diagonal C ε hF]
  have hneg : -(∑ a, C a a)≤∑ a, |C a a| := by
    rw [←Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun a _ => neg_le_abs _
  have hdiag : (∑ a, |C a a|)≤∑ a, ∑ b, |C a b| := by
    apply Finset.sum_le_sum
    intro a _
    exact Finset.single_le_sum (fun b _ => abs_nonneg (C a b)) (Finset.mem_univ a)
  linarith

/-- The full Gram coefficient mass is uniform in the number and choice of filters. -/
theorem GramFactors.matrix_mass_le_source {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (C : Fin (D+1) → Fin (D+1) → ℝ) {ε : ℝ}
    (hε : 0≤ε) (hF : ∀ θ, F θ= -coefficientSymbol C θ-ε) :
    (∑ a, ∑ b, |cert.matrix a b|)≤(D+1 : ℕ)*(∑ a, ∑ b, |C a b|) :=
  cert.matrix_mass_le.trans (mul_le_mul_of_nonneg_left
    (cert.trace_le_matrix_mass C hε hF) (by positivity))

end polyak.FiniteHorizon
