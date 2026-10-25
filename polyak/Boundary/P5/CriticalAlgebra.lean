import polyak.Boundary.P5.CriticalBounds

/-!
Article: Theorem p5h0, the exact seven critical equations.
Use: the displayed source primal equations and the three collected dual
polynomials vanish in the actual isolated root. Each identity is checked
as a polynomial multiple of q₅, then evaluated in ℝ.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5

/-- Article: critical source equation 0, after substituting the exact data. -/
def criticalEquation0 : ℚ[X] := Polynomial.C (-12)*APolynomial+Polynomial.C 4*DPolynomial+PPolynomial*(Polynomial.C 4*Polynomial.X^3-Polynomial.C 3*Polynomial.X-1)+Polynomial.C 2

/-- Article: exact q₅-divisibility of critical equation 0. -/
theorem critical_equation_0 : Polynomial.aeval y₀ criticalEquation0=0 := by
  norm_num [criticalEquation0,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-198165*y₀^2/4228 + 201519*y₀/8456 + 173781/8456) * y₀_equation

/-- Article: critical source equation 1, after substituting the exact data. -/
def criticalEquation1 : ℚ[X] := Polynomial.C (-6)*APolynomial+Polynomial.C 6*BPolynomial-Polynomial.C 4*DPolynomial+PPolynomial*(Polynomial.C 4*Polynomial.X^4-Polynomial.C 4*Polynomial.X^3-Polynomial.C 7*Polynomial.X^2+Polynomial.C 4*Polynomial.X+Polynomial.C 3)+Polynomial.C 4

/-- Article: exact q₅-divisibility of critical equation 1. -/
theorem critical_equation_1 : Polynomial.aeval y₀ criticalEquation1=0 := by
  norm_num [criticalEquation1,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-198165*y₀^3/4228 + 85407*y₀^2/1208 + 6582*y₀/151 - 286239/4228) * y₀_equation

/-- Article: critical source equation 2, after substituting the exact data. -/
def criticalEquation2 : ℚ[X] := Polynomial.C (-12)*BPolynomial-Polynomial.C 12*DPolynomial+PPolynomial*(Polynomial.C 16*Polynomial.X^5-Polynomial.C 16*Polynomial.X^4-Polynomial.C 24*Polynomial.X^3+Polynomial.C 16*Polynomial.X^2+Polynomial.C 9*Polynomial.X-1)+Polynomial.C 18

/-- Article: exact q₅-divisibility of critical equation 2. -/
theorem critical_equation_2 : Polynomial.aeval y₀ criticalEquation2=0 := by
  norm_num [criticalEquation2,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-198165*y₀^4/1057 + 85407*y₀^3/302 + 539019*y₀^2/4228 - 2088393*y₀/8456 + 261099/8456) * y₀_equation

/-- Article: critical source equation 3, after substituting the exact data. -/
def criticalEquation3 : ℚ[X] := Polynomial.C (-12)*APolynomial+Polynomial.C 24*BPolynomial-Polynomial.C 20*DPolynomial+Polynomial.C 50+PPolynomial*(Polynomial.C 64*Polynomial.X^7-Polynomial.C 64*Polynomial.X^6-Polynomial.C 128*Polynomial.X^5+Polynomial.C 112*Polynomial.X^4+Polynomial.C 80*Polynomial.X^3-Polynomial.C 56*Polynomial.X^2-Polynomial.C 15*Polynomial.X+Polynomial.C 7)

/-- Article: exact q₅-divisibility of critical equation 3. -/
theorem critical_equation_3 : Polynomial.aeval y₀ criticalEquation3=0 := by
  norm_num [criticalEquation3,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-792660*y₀^6/1057 + 170814*y₀^5/151 + 935349*y₀^4/1057 - 3680421*y₀^3/2114 + 45363*y₀^2/4228 + 5251539*y₀/8456 - 194229/1208) * y₀_equation

/-- Article: critical source equation 4, after substituting the exact data. -/
def criticalEquation4 : ℚ[X] := w2Polynomial*(Polynomial.C (-6 : ℚ)+Polynomial.C ((-129/4) : ℚ)*Polynomial.X+Polynomial.C (-48 : ℚ)*Polynomial.X^2+Polynomial.C (27 : ℚ)*Polynomial.X^3+Polynomial.C (96 : ℚ)*Polynomial.X^4+Polynomial.C (-48 : ℚ)*Polynomial.X^6)+w3Polynomial*(Polynomial.C ((13/2) : ℚ)+Polynomial.C (-16 : ℚ)*Polynomial.X+Polynomial.C (-78 : ℚ)*Polynomial.X^2+Polynomial.C (12 : ℚ)*Polynomial.X^3+Polynomial.C (116 : ℚ)*Polynomial.X^4+Polynomial.C (-48 : ℚ)*Polynomial.X^6)+(Polynomial.C ((-3/2) : ℚ)+Polynomial.C (21 : ℚ)*Polynomial.X+Polynomial.C (63 : ℚ)*Polynomial.X^2+Polynomial.C (-12 : ℚ)*Polynomial.X^3+Polynomial.C (-96 : ℚ)*Polynomial.X^4+Polynomial.C (48 : ℚ)*Polynomial.X^6)

/-- Article: exact q₅-divisibility of critical equation 4. -/
theorem critical_equation_4 : Polynomial.aeval y₀ criticalEquation4=0 := by
  norm_num [criticalEquation4,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-62337600*y₀^5/43243231 - 104528400*y₀^4/43243231 + 19445280*y₀^3/43243231 + 113780910*y₀^2/43243231 + 66413250*y₀/43243231 + 23554065/86486462) * y₀_equation

/-- Article: critical source equation 5, after substituting the exact data. -/
def criticalEquation5 : ℚ[X] := w2Polynomial*(Polynomial.C (-3 : ℚ))+w3Polynomial*(Polynomial.C (22 : ℚ))+(Polynomial.C (-12 : ℚ))

/-- Article: exact q₅-divisibility of critical equation 5. -/
theorem critical_equation_5 : Polynomial.aeval y₀ criticalEquation5=0 := by
  norm_num [criticalEquation5,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (0) * y₀_equation

/-- Article: critical source equation 6, after substituting the exact data. -/
def criticalEquation6 : ℚ[X] := w2Polynomial*(Polynomial.C ((-129/4) : ℚ)+Polynomial.C (-96 : ℚ)*Polynomial.X+Polynomial.C (81 : ℚ)*Polynomial.X^2+Polynomial.C (384 : ℚ)*Polynomial.X^3+Polynomial.C (-288 : ℚ)*Polynomial.X^5)+w3Polynomial*(Polynomial.C (-16 : ℚ)+Polynomial.C (-156 : ℚ)*Polynomial.X+Polynomial.C (36 : ℚ)*Polynomial.X^2+Polynomial.C (464 : ℚ)*Polynomial.X^3+Polynomial.C (-288 : ℚ)*Polynomial.X^5)+(Polynomial.C (21 : ℚ)+Polynomial.C (126 : ℚ)*Polynomial.X+Polynomial.C (-36 : ℚ)*Polynomial.X^2+Polynomial.C (-384 : ℚ)*Polynomial.X^3+Polynomial.C (288 : ℚ)*Polynomial.X^5)

/-- Article: exact q₅-divisibility of critical equation 6. -/
theorem critical_equation_6 : Polynomial.aeval y₀ criticalEquation6=0 := by
  norm_num [criticalEquation6,APolynomial,BPolynomial,DPolynomial,PPolynomial,
    w2Polynomial,w3Polynomial]
  linear_combination (-374025600*y₀^4/43243231 - 627170400*y₀^3/43243231 - 138912480*y₀^2/43243231 + 155937300*y₀/43243231 + 57677070/43243231) * y₀_equation

/-- Article: the three critical upper-lag weights have exactly unit mass. -/
theorem critical_weights_sum : w2₀+w3₀+w5₀=1 := by
  norm_num [w2₀,w3₀,w5₀,w2Polynomial,w3Polynomial,w5Polynomial]
  ring

/-- Article: the exact two linear relations among the critical dual weights. -/
theorem critical_weights_relations :
    w2₀=(2/5 : ℝ)-(22/25 : ℝ)*w5₀ ∧ w3₀=(3/5 : ℝ)-(3/25 : ℝ)*w5₀ := by
  norm_num [w2₀,w3₀,w5₀,w2Polynomial,w3Polynomial,w5Polynomial]
  constructor <;> ring

/-- Article: the four displayed critical primal equations, in the original real data. -/
theorem critical_primal_equations :
    -12*A₀+4*D₀+P₀*(4*y₀^3-3*y₀-1)+2=0 ∧
    -6*A₀+6*B₀-4*D₀+P₀*(4*y₀^4-4*y₀^3-7*y₀^2+4*y₀+3)+4=0 ∧
    -12*B₀-12*D₀+P₀*(16*y₀^5-16*y₀^4-24*y₀^3+16*y₀^2+9*y₀-1)+18=0 ∧
    -12*A₀+24*B₀-20*D₀+50+
      P₀*(64*y₀^7-64*y₀^6-128*y₀^5+112*y₀^4+80*y₀^3-56*y₀^2-15*y₀+7)=0 := by
  have h0 := critical_equation_0
  have h1 := critical_equation_1
  have h2 := critical_equation_2
  have h3 := critical_equation_3
  norm_num [criticalEquation0] at h0
  norm_num [criticalEquation1] at h1
  norm_num [criticalEquation2] at h2
  norm_num [criticalEquation3] at h3
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [A₀,D₀,P₀,neg_mul] using h0
  · simpa only [A₀,B₀,D₀,P₀,neg_mul] using h1
  · simpa only [B₀,D₀,P₀,neg_mul] using h2
  · simpa only [A₀,B₀,D₀,P₀,neg_mul] using h3

end polyak.Boundary.P5
