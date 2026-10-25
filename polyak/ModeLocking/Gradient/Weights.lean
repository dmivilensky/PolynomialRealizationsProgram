import polyak.ModeLocking.Gradient.LagDifferential

/-! The averaging weights in the article are strictly positive and normalized,
and arise from differentiating the actual class-sum symbol. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Continuation
open scoped BigOperators
variable {q:Tuning} {s:ℝ} {L:ℕ} (D:RegularData q s L)

def symbolShiftCoefficient (i:Fin D.d) : ℝ :=
  Real.sin (Geometry.shiftedCurve q s (D.atoms i))*pinningPolynomial D.lags D.dual (D.atoms i)

theorem symbolShiftCoefficient_pos (i:Fin D.d) : 0<D.symbolShiftCoefficient i :=
  mul_pos (Localization.phase_sin_pos q s (D.atoms i)
    ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩) (D.pinning_pos i)

theorem class_derivative_sum (i:Fin D.d) :
    (∑r,D.classWeight r*deriv (fun t=>(Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)) s)=
      D.symbolShiftCoefficient i := by
  have he : (fun t=>∑r,D.classWeight r*(Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i))=
      (fun t=>finiteSymbol q t D.lags D.dual (D.atoms i)) := by
    funext t
    exact D.class_sum_symbol_at t (D.atoms i) (D.atoms_grid i)
  have hd := HasDerivAt.fun_sum (u:=Finset.univ) (fun r _=>
    ((hasDerivAt_lag_shift q s (D.reps r) (D.atoms i)
      ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩).differentiableAt.hasDerivAt).const_mul (D.classWeight r))
  rw [he] at hd
  exact hd.unique (hasDerivAt_finiteSymbol_shift q s D.lags D.dual (D.atoms i)
    ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩ (D.symbol_zero_support i))

def gradientMass (i:Fin D.d) : ℝ := (D.primal i:ℝ)*D.symbolShiftCoefficient i

def gradientTotal : ℝ := ∑i,D.gradientMass i

def gradientWeight (i:Fin D.d) : ℝ := D.gradientMass i/D.gradientTotal

theorem gradientMass_pos (i:Fin D.d) : 0<D.gradientMass i :=
  mul_pos (by exact_mod_cast D.primal_pos i) (D.symbolShiftCoefficient_pos i)

theorem gradientTotal_pos : 0<D.gradientTotal :=
  Finset.sum_pos' (fun i _=>(D.gradientMass_pos i).le)
    ⟨⟨0,D.d_pos⟩,Finset.mem_univ _,D.gradientMass_pos _⟩

theorem gradientWeight_pos (i:Fin D.d) : 0<D.gradientWeight i :=
  div_pos (D.gradientMass_pos i) D.gradientTotal_pos

theorem gradientWeight_sum : (∑i,D.gradientWeight i)=1 := by
  change (∑i,D.gradientMass i/D.gradientTotal)=1
  rw [←Finset.sum_div]
  exact div_self D.gradientTotal_pos.ne'

end polyak.ModeLocking.RegularData
