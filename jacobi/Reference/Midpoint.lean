import jacobi.Reference.EigenEquation
import jacobi.Jacobi.RestoringState

/-!
Article: jacobi, Proposition C.2.
The actual source reference functions split into their exact Neumann
and Dirichlet midpoint classes. The complementary midpoint values are
nonzero, proved from genuine polynomial root simplicity. Thus parity
does not merely provide a possible vanishing boundary condition.
Use: proves strict separation of the two reference midpoint boundary classes and the nonzero boundary normalization factors.
-/
namespace jacobi.Reference
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference wave and its actual slope never vanish simultaneously in the physical interior.
Use: proves strict separation of the two reference midpoint boundary classes and the nonzero boundary normalization factors.
Article: jacobi, Proposition C.2.
Proof: a wave zero is an actual zero of the original normalized Jacobi polynomial. Its genuine derivative is nonzero by the proved root-simplicity theorem; the physical weight, sine and pi factors are strictly positive. -/
theorem eigenfunction_state_nonzero {a : ℝ} (ha : -1<a) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    eigenfunction a k t≠0 ∨ eigenfunctionSlope a k t≠0 := by
  -- The actual reference polynomial and its proved simple zeros supply state nontriviality without an ODE certificate premise.
  by_cases hz : eigenfunction a k t=0
  · right
    have hw := weight_pos a ht
    have hp : jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)=0 :=
      (mul_eq_zero.mp hz).resolve_left hw.ne'
    have hder := jacobi.Jacobi.shifted_root_derivative_ne_zero (parameters ha).2 (parameters ha).2 k hp
    rw [eigenfunctionSlope,hp,mul_zero,add_zero,jacobi.Jacobi.angularSlope]
    exact mul_ne_zero hw.ne' (mul_ne_zero Real.pi_ne_zero
      (mul_ne_zero (div_pos (sine_pos ht) (by norm_num)).ne' hder))
  · exact Or.inl hz

/-- Every odd-degree original reference eigenfunction has its exact Dirichlet midpoint value zero.
Use: identifies the source's even one-based reference spectral class at the physical midpoint.
Article: jacobi, Proposition C.2.
Proof: evaluate the genuine odd midpoint reflection at its fixed point. -/
theorem midpoint_dirichlet {a : ℝ} (ha : -1<a) (k : ℕ) : eigenfunction a (2*k+1) (1/2)=0 := by
  have h := eigenfunction_reflection ha (2*k+1) (1/2)
  have he : (-1:ℝ)^(2*k+1)= -1 := by rw [pow_add,pow_mul]; norm_num
  rw [he,show (1:ℝ)-1/2=1/2 by norm_num] at h
  linarith

/-- Every even-degree original reference eigenfunction has its exact Neumann midpoint derivative zero.
Use: identifies the source's odd one-based reference spectral class with the actual midpoint Neumann condition.
Article: jacobi, Proposition C.2.
Proof: differentiate the actual even midpoint reflection at its fixed point. Uniqueness of the two genuine ordinary derivatives forces the slope to equal its negative. -/
theorem midpoint_neumann {a : ℝ} (ha : -1<a) (k : ℕ) : eigenfunctionSlope a (2*k) (1/2)=0 := by
  -- Both derivatives belong to the actual original reference function, whose smoothness has already been proved.
  have he : (-1:ℝ)^(2*k)=1 := by rw [pow_mul]; norm_num
  have href : (fun t : ℝ => eigenfunction a (2*k) (1-t))=eigenfunction a (2*k) := by
    funext t
    simpa only [he,one_mul] using eigenfunction_reflection ha (2*k) t
  have hd := eigenfunction_hasDerivAt a (2*k) (t := (1/2:ℝ)) (by norm_num)
  have hr := (eigenfunction_hasDerivAt a (2*k) (t := (1:ℝ)-1/2) (by norm_num)).comp (1/2)
    ((hasDerivAt_const (1/2:ℝ) (1:ℝ)).sub (hasDerivAt_id (1/2:ℝ)))
  change HasDerivAt (fun t : ℝ => eigenfunction a (2*k) (1-t))
    (eigenfunctionSlope a (2*k) (1-1/2)*(0-1)) (1/2) at hr
  rw [href,show (1:ℝ)-1/2=1/2 by norm_num] at hr
  have hh := hr.unique hd
  linarith

/-- The genuine reference midpoint classes have exactly one vanishing coordinate, with the other coordinate strictly nonzero.
Use: supplies the original Neumann/Dirichlet reference split used to identify the transformed midpoint boundary conditions in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: combine the proved genuine boundary conditions with the actual nonvanishing two-dimensional reference state. -/
theorem midpoint_classes {a : ℝ} (ha : -1<a) (k : ℕ) :
    (eigenfunctionSlope a (2*k) (1/2)=0 ∧ eigenfunction a (2*k) (1/2)≠0) ∧
      (eigenfunction a (2*k+1) (1/2)=0 ∧ eigenfunctionSlope a (2*k+1) (1/2)≠0) := by
  have hn := midpoint_neumann ha k
  have hd := midpoint_dirichlet ha k
  exact ⟨⟨hn,(eigenfunction_state_nonzero ha (2*k) (by norm_num)).resolve_right (not_not.mpr hn)⟩,
    ⟨hd,(eigenfunction_state_nonzero ha (2*k+1) (by norm_num)).resolve_left (not_not.mpr hd)⟩⟩

end
end jacobi.Reference
