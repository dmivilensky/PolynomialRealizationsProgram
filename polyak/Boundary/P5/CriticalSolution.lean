import polyak.Boundary.P5.CriticalSystem

/-!
Article: Theorem p5h0, the exact critical point solves the actual regularized system.
Use: the analytic implicit function theorem is based at a proved zero of F,
not a candidate supplied as an extra hypothesis.
-/
noncomputable section
namespace polyak.Boundary.P5

/-- Article: the exact critical data solve source equation 0. -/
theorem criticalSource_solution_0 : polynomialValue C0 criticalPoint=0 := by
  have h : Polynomial.aeval y₀ criticalEquation0/4=0 := by rw [critical_equation_0,zero_div]
  convert h using 1
  norm_num [C0,C0Part0,polynomialValue,criticalEquation0]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 1. -/
theorem criticalSource_solution_1 : polynomialValue C1 criticalPoint=0 := by
  have h := critical_equation_1
  convert h using 1
  norm_num [C1,C1Part0,polynomialValue,criticalEquation1]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 2. -/
theorem criticalSource_solution_2 : polynomialValue C2 criticalPoint=0 := by
  have h := critical_equation_2
  convert h using 1
  norm_num [C2,C2Part0,polynomialValue,criticalEquation2]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 3. -/
theorem criticalSource_solution_3 : polynomialValue C3 criticalPoint=0 := by
  have h := critical_equation_3
  convert h using 1
  norm_num [C3,C3Part0,polynomialValue,criticalEquation3]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 4. -/
theorem criticalSource_solution_4 : polynomialValue C4 criticalPoint=0 := by
  have h := critical_equation_4
  convert h using 1
  norm_num [C4,C4Part0,C4Part1,polynomialValue,criticalEquation4]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 5. -/
theorem criticalSource_solution_5 : polynomialValue C5 criticalPoint=0 := by
  have h := critical_equation_5
  convert h using 1
  norm_num [C5,C5Part0,polynomialValue,criticalEquation5]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the exact critical data solve source equation 6. -/
theorem criticalSource_solution_6 : polynomialValue C6 criticalPoint=0 := by
  have h := critical_equation_6
  convert h using 1
  norm_num [C6,C6Part0,C6Part1,polynomialValue,criticalEquation6]
  dsimp only [A₀,B₀,D₀,P₀,w2₀,w3₀]
  ring

/-- Article: the full actual regularized source system vanishes at the critical data. -/
theorem regularSystem_criticalPoint : regularSystem (0,criticalPoint)=0 := by
  rw [regularSystem_zero]
  ext i
  fin_cases i
  · exact criticalSource_solution_0
  · exact criticalSource_solution_1
  · exact criticalSource_solution_2
  · exact criticalSource_solution_3
  · exact criticalSource_solution_4
  · exact criticalSource_solution_5
  · exact criticalSource_solution_6

end polyak.Boundary.P5
