import polyak.FiniteHorizon.FactorizationConstructors
import polyak.Boundary.P5.NormalizedDual

/-!
Article: Appendix C, constructive factors of the nonnegative divided differences
appearing when the twist is increased above the actual boundary. All selected
lags are two, three or five; the real filter widths remain at most four.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Boundary Spectral

def tDivTwo (G c : ℝ) : ℝ := 2*(G+c)
def tDivThree (G c : ℝ) : ℝ := 4*(G^2+G*c+c^2)-3
def tDivFive (G c : ℝ) : ℝ :=
  16*(G^4+G^3*c+G^2*c^2+G*c^3+c^4)-20*(G^2+G*c+c^2)+5
def uDivOne (_G _c : ℝ) : ℝ := 2
def uDivTwo (G c : ℝ) : ℝ := 4*(G+c)
def uDivFour (G c : ℝ) : ℝ := (G+c)*(16*G^2+16*c^2-12)

def tDivTwoFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 1 (fun θ => tDivTwo G (frequencyCosine θ)) :=
  ((reflectedGapFactorization hG).scale (r:=2) (by norm_num)).congr
    (fun θ => by rfl)

def tDivThreeFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 2 (fun θ => tDivThree G (frequencyCosine θ)) := by
  have h0:=linearSquareFactorization 1 2
  have h1:=((reflectedGapFactorization (G:=G+1) (by linarith)).scale
    (r:=4*(G-1)) (by positivity)).widen (show 1≤2 by omega)
  exact (h0.add h1).congr (fun θ => by unfold tDivThree; ring)

/-- The odd fifth-order endpoint kernel is the square of a real quadratic. -/
def tDivFiveBaseFactorization :
    SquareFactorization 4 (fun θ => (4*frequencyCosine θ^2+2*frequencyCosine θ-1)^2) := by
  let x:=(-1-Real.sqrt 5)/4
  let y:=(-1+Real.sqrt 5)/4
  have h:=(doubleContactFactorization x y).scale (r:=16) (by norm_num)
  exact h.congr (fun θ => by
    have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤5)
    have hf : 4*(frequencyCosine θ-x)*(frequencyCosine θ-y)=
        4*frequencyCosine θ^2+2*frequencyCosine θ-1 := by dsimp [x,y]; nlinarith
    calc
      _=(4*(frequencyCosine θ-x)*(frequencyCosine θ-y))^2 := by ring
      _=_ := by rw [hf])

/-- The first variation of the fifth-order kernel is itself a positive cubic. -/
def tDivFiveLinearFactorization :
    SquareFactorization 3 (fun θ =>
      16*frequencyCosine θ^3+32*frequencyCosine θ^2+28*frequencyCosine θ+24) := by
  have h0:=(linearSquareFactorization (1/2) 1).scale (r:=16) (by norm_num)
  have h1:=(constantFactorization (a:=8) (by norm_num)).widen (show 0≤2 by omega)
  have h2:=one_add_cosine.mul (h0.add h1)
  have h3:=(constantFactorization (a:=12) (by norm_num)).widen (show 0≤3 by omega)
  exact (h2.add h3).congr (fun θ => by ring)

/-- The full fifth-order divided difference is a finite sum of real squares. -/
def tDivFiveFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 4 (fun θ => tDivFive G (frequencyCosine θ)) := by
  have hh : 0≤G-1:=by linarith
  have h0:=tDivFiveBaseFactorization
  have h1:=(tDivFiveLinearFactorization.scale hh).widen (show 3≤4 by omega)
  have h2:=((quadraticReserveFactorization (a:=76) (b:=48) (d:=16) (by norm_num)).scale
    (r:=(G-1)^2) (sq_nonneg _)).widen (show 2≤4 by omega)
  have h3:=((reflectedGapFactorization (G:=4) (by norm_num)).scale
    (r:=16*(G-1)^3) (by positivity)).widen (show 1≤4 by omega)
  have h4:=(constantFactorization (a:=16*(G-1)^4) (by positivity)).widen
    (show 0≤4 by omega)
  exact ((((h0.add h1).add h2).add h3).add h4).congr (fun θ => by
    unfold tDivFive
    ring)

def uDivOneFactorization (G : ℝ) :
    SquareFactorization 0 (fun θ => uDivOne G (frequencyCosine θ)) :=
  constantFactorization (a:=2) (by norm_num)

def uDivTwoFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 1 (fun θ => uDivTwo G (frequencyCosine θ)) :=
  (reflectedGapFactorization hG).scale (r:=4) (by norm_num)

def uDivFourFactorization {G : ℝ} (hG : 1≤G) :
    SquareFactorization 3 (fun θ => uDivFour G (frequencyCosine θ)) := by
  have h0:=(cosineSquareFactorization.scale (r:=16) (by norm_num)).add
    ((constantFactorization (a:=16*G^2-12) (by nlinarith)).widen (show 0≤2 by omega))
  exact ((reflectedGapFactorization hG).mul h0).congr
    (fun θ => by unfold uDivFour; ring)

/-- The actual evaluated α for the selected lag set. -/
def selectedAlpha (G w₂ w₃ c : ℝ) : ℝ := 1+
  w₂/(2*G)*tDivTwo G c+w₃/(4*G^2-1)*tDivThree G c+
    (1-w₂-w₃)/(16*G^4-12*G^2+1)*tDivFive G c

/-- The actual evaluated β for the selected lag set. -/
def selectedBeta (G w₂ w₃ c : ℝ) : ℝ :=
  w₂/(2*G)*uDivOne G c+w₃/(4*G^2-1)*uDivTwo G c+
    (1-w₂-w₃)/(16*G^4-12*G^2+1)*uDivFour G c

theorem selected_symbol_factor {G : ℝ} (hG : 1≤G) (u w₂ w₃ : ℝ)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) (c : ℝ) :
    dualSymbol (P5.weights235 w₂ w₃ h₂ h₃ h₅) u G c=
      (G-c)*((1-c^2-u^2)*selectedAlpha G w₂ w₃ c-
        2*u*(1-c^2)*selectedBeta G w₂ w₃ c) := by
  have h0 : G≠0:=by linarith
  have h2 : 4*G^2-1≠0:=by nlinarith
  have h4 : 16*G^4-12*G^2+1≠0:=by
    have h:=P5.commonDenominator_pos hG
    intro he
    rw [he,mul_zero] at h
    exact (lt_irrefl 0) h
  have h2' : G^2*4-1≠0:=by nlinarith
  have h2'' : -1+G^2*4≠0:=by nlinarith
  have h4' : G^2*(G^2*16-12)+1≠0:=by convert h4 using 1; ring
  have h4'' : 1-G^2*12+G^4*16≠0:=by convert h4 using 1; ring
  rw [P5.dualSymbol_weights235,normalizedLower_one,normalizedUpper_two,
    normalizedUpper_three,P5.normalizedUpper_five]
  unfold g selectedAlpha selectedBeta tDivTwo tDivThree tDivFive uDivOne uDivTwo uDivFour
  field_simp [h0,h2,h2',h2'',h4,h4',h4'']
  ring

/-- α−1 has an exact width-four factorization for every actual simplex vector. -/
def selectedAlphaReserveFactorization {G w₂ w₃ : ℝ} (hG : 1≤G)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) :
    SquareFactorization 4 (fun θ => selectedAlpha G w₂ w₃ (frequencyCosine θ)-1) := by
  have hden : 0<16*G^4-12*G^2+1:=by
    have h:=P5.commonDenominator_pos hG
    have ha : 0<G*(4*G^2-1):=mul_pos (by linarith) (by nlinarith)
    exact (mul_pos_iff_of_pos_left ha).mp h
  have h0:=((tDivTwoFactorization hG).scale
    (r:=w₂/(2*G)) (div_nonneg h₂ (by positivity))).widen (show 1≤4 by omega)
  have h1:=((tDivThreeFactorization hG).scale
    (r:=w₃/(4*G^2-1)) (div_nonneg h₃ (by nlinarith))).widen (show 2≤4 by omega)
  have h2:=(tDivFiveFactorization hG).scale
    (r:=(1-w₂-w₃)/(16*G^4-12*G^2+1)) (div_nonneg h₅ hden.le)
  exact ((h0.add h1).add h2).congr (fun θ => by unfold selectedAlpha; ring)

/-- β has an exact width-three factorization for every actual simplex vector. -/
def selectedBetaFactorization {G w₂ w₃ : ℝ} (hG : 1≤G)
    (h₂ : 0≤w₂) (h₃ : 0≤w₃) (h₅ : 0≤1-w₂-w₃) :
    SquareFactorization 3 (fun θ => selectedBeta G w₂ w₃ (frequencyCosine θ)) := by
  have hden : 0<16*G^4-12*G^2+1:=by
    have h:=P5.commonDenominator_pos hG
    have ha : 0<G*(4*G^2-1):=mul_pos (by linarith) (by nlinarith)
    exact (mul_pos_iff_of_pos_left ha).mp h
  have h0:=((uDivOneFactorization G).scale
    (r:=w₂/(2*G)) (div_nonneg h₂ (by positivity))).widen (show 0≤3 by omega)
  have h1:=((uDivTwoFactorization hG).scale
    (r:=w₃/(4*G^2-1)) (div_nonneg h₃ (by nlinarith))).widen (show 1≤3 by omega)
  have h2:=(uDivFourFactorization hG).scale
    (r:=(1-w₂-w₃)/(16*G^4-12*G^2+1)) (div_nonneg h₅ hden.le)
  exact ((h0.add h1).add h2).congr (fun θ => by unfold selectedBeta; ring)

end polyak.FiniteHorizon
