import polyak.FiniteHorizon.Factorization

/-!
Article: Appendix C, constructive real factors of the actual low-degree symbols.
Use: constants, affine cosine factors, quadratic reserves and polynomial squares
give finite filters without an assumed general spectral factorization theorem.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy

/-- The real cosine coordinate on the normalized frequency circle. -/
def frequencyCosine (θ : FrequencyCircle) : ℝ := (character 1 θ).re

theorem character_two_re (θ : FrequencyCircle) :
    (character 2 θ).re=2*frequencyCosine θ^2-1 := by
  have h:=character_re_mul_re 1 1 θ
  norm_num only [Int.reduceAdd,Int.reduceSub,character,fourier_zero,
    Complex.one_re] at h
  change frequencyCosine θ*frequencyCosine θ=(_+1)/2 at h
  nlinarith

theorem linear_filter_square (a b : ℝ) (θ : FrequencyCircle) :
    filterSquare [(b/2,0),(a,1),(b/2,2)] θ=(a+b*frequencyCosine θ)^2 := by
  simp only [filterSquare,filterOuter,kernelSymbol,List.flatMap_cons,List.flatMap_nil,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.sum_cons,List.sum_nil,Int.reduceSub]
  simp only [character,fourier_zero,fourier_neg,Complex.one_re,Complex.conj_re]
  rw [show (fourier (2 : ℤ) θ).re=2*frequencyCosine θ^2-1 from character_two_re θ]
  unfold frequencyCosine
  ring

/-- A real affine polynomial squared has a causal real filter of width two. -/
def linearSquareFactorization (a b : ℝ) :
    SquareFactorization 2 (fun θ => (a+b*frequencyCosine θ)^2) where
  terms:=[(1,[(b/2,0),(a,1),(b/2,2)])]
  weight_nonneg term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    norm_num
  within term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> norm_num
  exact θ:=by
    simp only [weightedSquares,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,one_mul]
    exact (linear_filter_square a b θ).symm

theorem binomial_filter_square (a b : ℝ) (θ : FrequencyCircle) :
    filterSquare [(a,0),(b,1)] θ=a^2+b^2+2*a*b*frequencyCosine θ := by
  simp [filterSquare,filterOuter,kernelSymbol,character,frequencyCosine,
    AddCircle.toCircle_neg]
  ring

/-- The two elementary affine symbols are exact squared first differences. -/
def affineFactorization (s : ℝ) :
    SquareFactorization 1 (fun θ => 1+s^2+2*s*frequencyCosine θ) where
  terms:=[(1,[(1,0),(s,1)])]
  weight_nonneg term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    norm_num
  within term ht:=by
    simp only [List.mem_singleton] at ht
    subst term
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> norm_num
  exact θ:=by
    simp only [weightedSquares,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,one_mul]
    rw [binomial_filter_square]
    ring

def one_add_cosine : SquareFactorization 1 (fun θ => 1+frequencyCosine θ) := by
  have h:=(affineFactorization 1).scale (r:=1/2) (by norm_num)
  exact h.congr (fun θ => by ring)

def one_sub_cosine : SquareFactorization 1 (fun θ => 1-frequencyCosine θ) := by
  have h:=(affineFactorization (-1)).scale (r:=1/2) (by norm_num)
  exact h.congr (fun θ => by ring)

/-- G-c has a real width-one factorization for every G≥1. -/
def gapFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 1 (fun θ => G-frequencyCosine θ) := by
  have h:=(constantFactorization (a:=G-1) (by linarith)).widen (show 0≤1 by omega)
  exact (h.add one_sub_cosine).congr (fun θ => by ring)

/-- The reflected affine factor is equally constructive. -/
def reflectedGapFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 1 (fun θ => G+frequencyCosine θ) := by
  have h:=(constantFactorization (a:=G-1) (by linarith)).widen (show 0≤1 by omega)
  exact (h.add one_add_cosine).congr (fun θ => by ring)

/-- The sine square is the product of the two endpoint gaps. -/
def sineSquareFactorization : SquareFactorization 2 (fun θ => 1-frequencyCosine θ^2) :=
  (one_sub_cosine.mul one_add_cosine).congr (fun θ => by ring)

def cosineSquareFactorization : SquareFactorization 2 (fun θ => frequencyCosine θ^2) :=
  (linearSquareFactorization 0 1).congr (fun θ => by ring)

/-- A signed linear term with its exact absolute reserve. -/
def signedLinearFactorization (b : ℝ) :
    SquareFactorization 1 (fun θ => |b|+b*frequencyCosine θ) := by
  by_cases hb : 0≤b
  · exact (one_add_cosine.scale hb).congr (fun θ => by rw [abs_of_nonneg hb]; ring)
  · have hb' : 0≤-b:=by linarith
    exact (one_sub_cosine.scale hb').congr (fun θ => by
      rw [abs_of_neg (lt_of_not_ge hb)]
      ring)

/-- A signed quadratic term also admits a real width-two representation. -/
def signedQuadraticFactorization (b : ℝ) :
    SquareFactorization 2 (fun θ => |b|+b*frequencyCosine θ^2) := by
  by_cases hb : 0≤b
  · have h:=(constantFactorization hb).widen (show 0≤2 by omega)
    exact (h.add (cosineSquareFactorization.scale hb)).congr (fun θ => by
      rw [abs_of_nonneg hb])
  · have hb' : 0≤-b:=by linarith
    exact (sineSquareFactorization.scale hb').congr (fun θ => by
      rw [abs_of_neg (lt_of_not_ge hb)]
      ring)

/-- The strict reserve proved for the actual P₅ residual gives explicit factors. -/
def quadraticReserveFactorization {a b d : ℝ} (h : |b|+|d|≤a) :
    SquareFactorization 2 (fun θ => d*frequencyCosine θ^2+b*frequencyCosine θ+a) := by
  have h0:=(constantFactorization (a:=a-|b|-|d|) (by linarith)).widen (show 0≤2 by omega)
  have h1:=(signedLinearFactorization b).widen (show 1≤2 by omega)
  exact ((h0.add h1).add (signedQuadraticFactorization d)).congr (fun θ => by ring)

/-- The one-atom residual needs only its linear reserve when the leading
coefficient is nonnegative, exactly as in the source P₁ certificate. -/
def quadraticPositiveLeadingFactorization {a b d : ℝ} (hd : 0≤d) (h : |b|≤a) :
    SquareFactorization 2 (fun θ => d*frequencyCosine θ^2+b*frequencyCosine θ+a) := by
  have h0:=(constantFactorization (a:=a-|b|) (by linarith)).widen (show 0≤2 by omega)
  have h1:=(signedLinearFactorization b).widen (show 1≤2 by omega)
  exact ((h0.add h1).add (cosineSquareFactorization.scale hd)).congr (fun θ => by ring)

/-- Every real quadratic nonnegative on the frequency interval admits a real
causal factorization of width two. This finite-dimensional factorization is
proved by its two endpoint expansions or its exact vertex minimum. -/
def quadraticNonnegativeFactorization (a b d : ℝ)
    (hq : ∀ c : ℝ, -1≤c → c≤1 → 0≤d*c^2+b*c+a) :
    SquareFactorization 2 (fun θ => d*frequencyCosine θ^2+b*frequencyCosine θ+a) := by
  have hm:=hq (-1) (by norm_num) (by norm_num)
  have hp:=hq 1 (by norm_num) (by norm_num)
  by_cases hd : 0≤d
  · by_cases hb : 2*d≤b
    · have h0:=(linearSquareFactorization 1 1).scale hd
      have h1:=((one_add_cosine.scale (r:=b-2*d) (by linarith))).widen (show 1≤2 by omega)
      have h2:=(constantFactorization (a:=a-b+d) (by nlinarith)).widen (show 0≤2 by omega)
      exact ((h0.add h1).add h2).congr (fun θ => by ring)
    · by_cases hb' : b≤ -2*d
      · have h0:=(linearSquareFactorization 1 (-1)).scale hd
        have h1:=((one_sub_cosine.scale (r:=-b-2*d) (by linarith))).widen (show 1≤2 by omega)
        have h2:=(constantFactorization (a:=a+b+d) (by nlinarith)).widen (show 0≤2 by omega)
        exact ((h0.add h1).add h2).congr (fun θ => by ring)
      · have hd0 : 0<d:=by
          by_contra h
          have he : d=0:=by linarith
          rw [he] at hb hb'
          linarith
        let c₀:=-b/(2*d)
        have hc₀ : -1≤c₀ ∧ c₀≤1 := by
          dsimp [c₀]
          constructor
          · apply (le_div_iff₀ (by positivity : 0<2*d)).mpr
            linarith
          · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
            linarith
        have hmin:=hq c₀ hc₀.1 hc₀.2
        have hmin' : 0≤a-b^2/(4*d) := by
          have he : d*c₀^2+b*c₀+a=a-b^2/(4*d) := by dsimp [c₀]; field_simp [hd0.ne']; ring
          rwa [he] at hmin
        have h0:=(linearSquareFactorization (b/(2*d)) 1).scale hd
        have h1:=(constantFactorization hmin').widen (show 0≤2 by omega)
        exact (h0.add h1).congr (fun θ => by field_simp [hd0.ne']; ring)
  · have hd' : 0≤-d:=by linarith
    have h0:=((one_sub_cosine.scale (r:=(a-b+d)/2) (by nlinarith))).widen (show 1≤2 by omega)
    have h1:=((one_add_cosine.scale (r:=(a+b+d)/2) (by nlinarith))).widen (show 1≤2 by omega)
    exact ((h0.add h1).add (sineSquareFactorization.scale hd')).congr (fun θ => by ring)

/-- The exact squared double contact uses four causal shifts. -/
def doubleContactFactorization (x y : ℝ) :
    SquareFactorization 4 (fun θ => (frequencyCosine θ-x)^2*(frequencyCosine θ-y)^2) :=
  ((linearSquareFactorization (-x) 1).mul (linearSquareFactorization (-y) 1)).congr
    (fun θ => by ring)

/-- A double contact times the proved positive quadratic has width six. -/
def sexticContactFactorization (x y : ℝ) {a b d : ℝ} (h : |b|+|d|≤a) :
    SquareFactorization 6 (fun θ => (frequencyCosine θ-x)^2*(frequencyCosine θ-y)^2*
      (d*frequencyCosine θ^2+b*frequencyCosine θ+a)) :=
  (doubleContactFactorization x y).mul (quadraticReserveFactorization h)

end polyak.FiniteHorizon
