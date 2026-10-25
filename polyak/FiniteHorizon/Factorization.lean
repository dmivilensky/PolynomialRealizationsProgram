import polyak.Energy.Kernel

/-!
Article: Appendix C, finite real sum-of-squares factorizations in Lemma telescoping.
Use: constructive filters retain their support, nonnegative weights and exact
frequency symbol. Products add widths; no infinite spectral factor is assumed.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy
open scoped BigOperators

/-- Real finite filters supported at the causal indices from zero through D. -/
def FilterWithin (D : ℕ) (L : LinearFilter) : Prop :=
  ∀ p ∈ L, 0 ≤ p.2 ∧ p.2 ≤ (D : ℤ)

/-- The complex value of a real finite filter on a unit Fourier wave. -/
def filterFourier (L : LinearFilter) (θ : FrequencyCircle) : ℂ :=
  (L.map fun p => (p.1 : ℂ)*character p.2 θ).sum

/-- The real symbol of the filter's squared Hilbert norm. -/
def filterSquare (L : LinearFilter) (θ : FrequencyCircle) : ℝ :=
  kernelSymbol (filterOuter L L) θ

@[simp] theorem filterFourier_append (L M : LinearFilter) (θ : FrequencyCircle) :
    filterFourier (L++M) θ=filterFourier L θ+filterFourier M θ := by
  simp [filterFourier]

theorem filterFourier_eq_eval (L : LinearFilter) (θ : FrequencyCircle) :
    filterFourier L θ=filterEval L (fun n => character n θ) 0 := by
  simp [filterFourier,filterEval,Complex.real_smul]

/-- Each finite filter represents a genuinely nonnegative squared norm. -/
theorem filterSquare_eq_normSq (L : LinearFilter) (θ : FrequencyCircle) :
    filterSquare L θ=Complex.normSq (filterFourier L θ) := by
  rw [filterSquare,kernelSymbol_eq_eval,kernelEval_outer,filterFourier_eq_eval,
    real_inner_self_eq_norm_sq,Complex.normSq_eq_norm_sq]

theorem filterSquare_nonneg (L : LinearFilter) (θ : FrequencyCircle) :
    0≤filterSquare L θ := by
  rw [filterSquare_eq_normSq]
  exact Complex.normSq_nonneg _

/-- Convolution of two real finite filters. -/
def filterProduct (L M : LinearFilter) : LinearFilter :=
  L.flatMap fun p => M.map fun q => (p.1*q.1,p.2+q.2)

theorem filterWithin_product {D E : ℕ} {L M : LinearFilter}
    (hL : FilterWithin D L) (hM : FilterWithin E M) :
    FilterWithin (D+E) (filterProduct L M) := by
  intro r hr
  obtain ⟨p,hp,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hr
  subst r
  have h₁:=hL p hp
  have h₂:=hM q hq
  constructor
  · exact add_nonneg h₁.1 h₂.1
  · simpa only [Nat.cast_add] using add_le_add h₁.2 h₂.2

theorem filterFourier_product (L M : LinearFilter) (θ : FrequencyCircle) :
    filterFourier (filterProduct L M) θ=filterFourier L θ*filterFourier M θ := by
  have hmap (p : ℝ×ℤ) :
      filterFourier (M.map fun q => (p.1*q.1,p.2+q.2)) θ=
        ((p.1 : ℂ)*character p.2 θ)*filterFourier M θ := by
    induction M with
    | nil => simp [filterFourier]
    | cons q M ih =>
      change ((p.1*q.1 : ℝ) : ℂ)*character (p.2+q.2) θ+
        filterFourier (M.map fun q => (p.1*q.1,p.2+q.2)) θ=
        ((p.1 : ℂ)*character p.2 θ)*
          ((q.1 : ℂ)*character q.2 θ+filterFourier M θ)
      rw [ih]
      simp only [character,fourier_add,Complex.ofReal_mul]
      ring
  induction L with
  | nil => simp [filterProduct,filterFourier]
  | cons p L ih =>
    change filterFourier ((M.map fun q => (p.1*q.1,p.2+q.2))++filterProduct L M) θ=_
    rw [filterFourier_append]
    change filterFourier (M.map fun q => (p.1*q.1,p.2+q.2)) θ+
      filterFourier (filterProduct L M) θ=
      ((p.1 : ℂ)*character p.2 θ+filterFourier L θ)*filterFourier M θ
    rw [hmap,ih]
    ring

/-- Multiplication of symbols is convolution of actual finite real filters. -/
theorem filterSquare_product (L M : LinearFilter) (θ : FrequencyCircle) :
    filterSquare (filterProduct L M) θ=filterSquare L θ*filterSquare M θ := by
  simp_rw [filterSquare_eq_normSq,filterFourier_product,Complex.normSq_mul]

/-- The exact finite nonnegative combination of squared-filter symbols. -/
def weightedSquares (terms : List (ℝ×LinearFilter)) (θ : FrequencyCircle) : ℝ :=
  (terms.map fun term => term.1*filterSquare term.2 θ).sum

/-- A constructive finite spectral factorization, permitting multiple real filters. -/
structure SquareFactorization (D : ℕ) (F : FrequencyCircle → ℝ) where
  terms : List (ℝ×LinearFilter)
  weight_nonneg : ∀ term ∈ terms, 0≤term.1
  within : ∀ term ∈ terms, FilterWithin D term.2
  exact : ∀ θ, F θ=weightedSquares terms θ

/-- Transport an exact certificate along a proved source identity. -/
def SquareFactorization.congr {D : ℕ} {F G : FrequencyCircle → ℝ}
    (cert : SquareFactorization D F) (h : ∀ θ, F θ=G θ) : SquareFactorization D G where
  terms:=cert.terms
  weight_nonneg:=cert.weight_nonneg
  within:=cert.within
  exact θ:=by rw [←h θ]; exact cert.exact θ

theorem SquareFactorization.nonneg {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : SquareFactorization D F) (θ : FrequencyCircle) : 0≤F θ := by
  rw [cert.exact]
  apply List.sum_nonneg
  intro value hv
  obtain ⟨term,ht,rfl⟩:=List.mem_map.mp hv
  exact mul_nonneg (cert.weight_nonneg term ht) (filterSquare_nonneg _ _)

/-- The same filters fit in every larger causal window. -/
def SquareFactorization.widen {D E : ℕ} {F : FrequencyCircle → ℝ}
    (cert : SquareFactorization D F) (h : D≤E) : SquareFactorization E F where
  terms:=cert.terms
  weight_nonneg:=cert.weight_nonneg
  within term ht p hp:=by
    obtain ⟨h₀,h₁⟩:=cert.within term ht p hp
    exact ⟨h₀,h₁.trans (Int.ofNat_le.mpr h)⟩
  exact:=cert.exact

/-- Adding exact factorizations concatenates their finite squared filters. -/
def SquareFactorization.add {D : ℕ} {F G : FrequencyCircle → ℝ}
    (left : SquareFactorization D F) (right : SquareFactorization D G) :
    SquareFactorization D (fun θ => F θ+G θ) where
  terms:=left.terms++right.terms
  weight_nonneg term ht:=by
    rcases List.mem_append.mp ht with ht|ht
    · exact left.weight_nonneg term ht
    · exact right.weight_nonneg term ht
  within term ht:=by
    rcases List.mem_append.mp ht with ht|ht
    · exact left.within term ht
    · exact right.within term ht
  exact θ:=by
    rw [left.exact,right.exact]
    simp [weightedSquares]

theorem weightedSquares_scale (r : ℝ) (terms : List (ℝ×LinearFilter)) (θ : FrequencyCircle) :
    weightedSquares (terms.map fun term => (r*term.1,term.2)) θ=r*weightedSquares terms θ := by
  induction terms with
  | nil => simp [weightedSquares]
  | cons term terms ih =>
    change r*term.1*filterSquare term.2 θ+
      weightedSquares (terms.map fun term => (r*term.1,term.2)) θ=
      r*(term.1*filterSquare term.2 θ+weightedSquares terms θ)
    rw [ih]
    ring

/-- A nonnegative scalar changes only the exact filter weights. -/
def SquareFactorization.scale {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : SquareFactorization D F) {r : ℝ} (hr : 0≤r) :
    SquareFactorization D (fun θ => r*F θ) where
  terms:=cert.terms.map fun term => (r*term.1,term.2)
  weight_nonneg term ht:=by
    obtain ⟨original,ho,rfl⟩:=List.mem_map.mp ht
    exact mul_nonneg hr (cert.weight_nonneg original ho)
  within term ht:=by
    obtain ⟨original,ho,rfl⟩:=List.mem_map.mp ht
    exact cert.within original ho
  exact θ:=by rw [weightedSquares_scale,cert.exact]

def squareTermsProduct (left right : List (ℝ×LinearFilter)) : List (ℝ×LinearFilter) :=
  left.flatMap fun p => right.map fun q => (p.1*q.1,filterProduct p.2 q.2)

theorem weightedSquares_product (left right : List (ℝ×LinearFilter)) (θ : FrequencyCircle) :
    weightedSquares (squareTermsProduct left right) θ=
      weightedSquares left θ*weightedSquares right θ := by
  have hm (p : ℝ×LinearFilter) :
      weightedSquares (right.map fun q => (p.1*q.1,filterProduct p.2 q.2)) θ=
        (p.1*filterSquare p.2 θ)*weightedSquares right θ := by
    induction right with
    | nil => simp [weightedSquares]
    | cons q right ih =>
      change p.1*q.1*filterSquare (filterProduct p.2 q.2) θ+
        weightedSquares (right.map fun q => (p.1*q.1,filterProduct p.2 q.2)) θ=
        (p.1*filterSquare p.2 θ)*(q.1*filterSquare q.2 θ+weightedSquares right θ)
      rw [ih,filterSquare_product]
      ring
  have ha (L M : List (ℝ×LinearFilter)) :
      weightedSquares (L++M) θ=weightedSquares L θ+weightedSquares M θ := by
    simp [weightedSquares]
  induction left with
  | nil => simp [squareTermsProduct,weightedSquares]
  | cons p left ih =>
    change weightedSquares ((right.map fun q => (p.1*q.1,filterProduct p.2 q.2))++
      squareTermsProduct left right) θ=_
    rw [ha,hm,ih]
    change _=(p.1*filterSquare p.2 θ+weightedSquares left θ)*weightedSquares right θ
    ring

/-- Products of constructive real factorizations add their support widths. -/
def SquareFactorization.mul {D E : ℕ} {F G : FrequencyCircle → ℝ}
    (left : SquareFactorization D F) (right : SquareFactorization E G) :
    SquareFactorization (D+E) (fun θ => F θ*G θ) where
  terms:=squareTermsProduct left.terms right.terms
  weight_nonneg term ht:=by
    obtain ⟨p,hp,ht⟩:=List.mem_flatMap.mp ht
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ht
    exact mul_nonneg (left.weight_nonneg p hp) (right.weight_nonneg q hq)
  within term ht:=by
    obtain ⟨p,hp,ht⟩:=List.mem_flatMap.mp ht
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ht
    exact filterWithin_product (left.within p hp) (right.within q hq)
  exact θ:=by rw [weightedSquares_product,left.exact,right.exact]

/-- Nonnegative constants have a width-zero real factorization. -/
def constantFactorization {a : ℝ} (ha : 0≤a) : SquareFactorization 0 (fun _ => a) where
  terms:=[(a,unitFilter)]
  weight_nonneg term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    exact ha
  within term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    simp [FilterWithin,unitFilter]
  exact θ:=by
    simp [weightedSquares,filterSquare,unitFilter,filterOuter,kernelSymbol,character]

end polyak.FiniteHorizon
