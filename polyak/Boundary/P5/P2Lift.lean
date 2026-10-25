import polyak.Boundary.P5.PhysicalRoot
import polyak.Boundary.P2.Arc
import polyak.Boundary.P2.Parameter

/-! Exact P2 coordinates in the original regularized P5 system.
The endpoint is identified by source equations, rather than by matching decimal proposals. -/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Polynomial

/-- The unchanged physical two-atom data, expressed in P5's regular coordinates. -/
def p2Lift (z : ℝ) : Coordinates := ![
  (P2.u z-1/2)/(P2.G z-1),(P2.x z+1/2)/(P2.G z-1),P2.y z,
  P2.p z/(P2.G z-1),P2.d z/(P2.G z-1),P2.W z,1-P2.W z]

theorem p2Lift_coordinates {z : ℝ} (hz : z∈P2.parameterInterval) :
    branchU (P2.G z-1) (p2Lift z)=P2.u z ∧
    branchX (P2.G z-1) (p2Lift z)=P2.x z ∧
    (P2.G z-1)*p2Lift z 3=P2.p z ∧
    (P2.G z-1)*p2Lift z 4=P2.d z := by
  have hh : P2.G z-1≠0 := by linarith [P2.one_lt_G hz]
  refine ⟨?_,?_,?_,?_⟩ <;> norm_num [branchU,branchX,p2Lift] <;> field_simp [hh] <;> ring

private theorem dualClosed23_factor (u G w c : ℝ) :
    (dualClosed u G w (1-w)).eval c=(16*G^4-12*G^2+1)*
      (-((1-c^2-u^2)*cubicAlpha G w c-2*u*(1-c^2)*quadraticBeta G w c)) := by
  norm_num [dualClosed,cubicAlpha,quadraticBeta]
  ring

theorem p2Lift_dual_factor {z : ℝ} (hz : z∈P2.parameterInterval) (c : ℝ) :
    (dualReal (P2.G z-1) (p2Lift z)).eval c=
      4*P2.G z*(1-P2.W z)*(16*P2.G z^4-12*P2.G z^2+1)*(P2.atomPolynomial z c)^2 := by
  have hu := (p2Lift_coordinates hz).1
  rw [dualReal_closed]
  change (dualClosed (branchU (P2.G z-1) (p2Lift z)) (1+(P2.G z-1))
    (P2.W z) (1-P2.W z)).eval c=_
  rw [hu,show 1+(P2.G z-1)=P2.G z by ring,dualClosed23_factor,P2.double_square_identity hz]
  ring

theorem p2Lift_dual_polynomial {z : ℝ} (hz : z∈P2.parameterInterval) :
    dualReal (P2.G z-1) (p2Lift z)=
      C (4*P2.G z*(1-P2.W z)*(16*P2.G z^4-12*P2.G z^2+1))*
        (Polynomial.X-C (P2.x z))^2*(Polynomial.X-C (P2.y z))^2 := by
  apply Polynomial.funext
  intro c
  rw [p2Lift_dual_factor hz,P2.atomPolynomial_factor hz]
  simp only [eval_mul,eval_C,eval_pow,eval_sub,eval_X]
  ring

/-- All three P5 double-contact equations hold on the entire P2 arc. -/
theorem p2Lift_dual_equations {z : ℝ} (hz : z∈P2.parameterInterval) :
    regularSystem (P2.G z-1,p2Lift z) 4=0 ∧
    regularSystem (P2.G z-1,p2Lift z) 5=0 ∧
    regularSystem (P2.G z-1,p2Lift z) 6=0 := by
  obtain ⟨hy,hx',hy'⟩ := regularSystem_dual_exact (P2.G z-1) (p2Lift z)
  have hx := (p2Lift_coordinates hz).2.1
  have hy0 : p2Lift z 2=P2.y z := rfl
  rw [hy0,p2Lift_dual_polynomial hz] at hy hy'
  change regularSystem (P2.G z-1,p2Lift z) 5=(dualReal _ _).derivative.eval (branchX (P2.G z-1) (p2Lift z)) at hx'
  rw [hx,p2Lift_dual_polynomial hz] at hx'
  constructor
  · simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C,sub_self,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero] using hy
  · constructor
    · simpa [derivative_mul,derivative_pow,derivative_sub,derivative_X,derivative_C] using hx'
    · simpa [derivative_mul,derivative_pow,derivative_sub,derivative_X,derivative_C] using hy'

/-- The P2 and P5 constructions use exactly the same probability measure. -/
theorem p2Lift_spectrum {z : ℝ} (hz : z∈P2.parameterInterval) (h1 : P2.zeta1≤z) :
    P2.spectrum z hz h1=twoAtomSpectrum (P2.p z) (P2.p_mem hz h1).1
      (P2.p_mem hz h1).2.le (P2.lowerFrequency z hz) (P2.upperFrequency z hz) := by
  unfold P2.spectrum twoAtomSpectrum
  congr 1
  · funext b
    cases b <;> rfl
  · funext b
    cases b <;> rfl

/-- Every original P2 raw source slack is the P5 source at the lifted coordinates. -/
theorem p2Lift_rawBranch {z : ℝ} (hz : z∈P2.parameterInterval) (h1 : P2.zeta1≤z)
    (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    rawBranch (P2.G z-1) (p2Lift z) n σ=P2.reducedSlack z n σ := by
  let t := Real.arcosh (P2.G z)
  have ht : Real.cosh t=P2.G z := Real.cosh_arcosh (P2.one_lt_G hz).le
  have htpos : 0<t := Real.arcosh_pos (P2.one_lt_G hz)
  have hr := signed_raw_twoAtomSpectrum (P2.p z) (P2.p_mem hz h1).1
    (P2.p_mem hz h1).2.le (P2.lowerFrequency z hz) (P2.upperFrequency z hz)
    (P2.u z) t (P2.d z) htpos.ne' n hn σ
  rw [← p2Lift_spectrum hz h1] at hr
  rw [P2.actual_reducedSlack hz h1 ht (Real.sinh_ne_zero.mpr htpos.ne') n hn σ,ht] at hr
  obtain ⟨hu,hx,hp,hd⟩ := p2Lift_coordinates hz
  unfold rawBranch
  change (1-(P2.G z-1)*p2Lift z 3)*actualRaw (branchU (P2.G z-1) (p2Lift z)) (1+(P2.G z-1)) n σ
      (branchX (P2.G z-1) (p2Lift z))+(P2.G z-1)*p2Lift z 3*actualRaw (branchU (P2.G z-1) (p2Lift z)) (1+(P2.G z-1)) n σ
      (p2Lift z 2)-σ*(P2.G z-1)*p2Lift z 4*lagDenominator (1+(P2.G z-1)) n=_
  rw [hu,hx,hp,show σ*(P2.G z-1)*p2Lift z 4=σ*((P2.G z-1)*p2Lift z 4) by ring,hd,
    show 1+(P2.G z-1)=P2.G z by ring]
  exact hr.symm

/-- The rational P2 endpoint is an exact zero of all seven original P5 equations. -/
theorem p2Endpoint_source : regularSystem ((P2.G P2.zetaA)-1,p2Lift P2.zetaA)=0 := by
  have hh : 0≤(P2.G P2.zetaA)-1 := by linarith [P2.one_lt_G P2.zetaA_mem]
  have hh0 : (P2.G P2.zetaA)-1≠0 := by linarith [P2.one_lt_G P2.zetaA_mem]
  have hp (n : ℕ) (hn : 1≤n) (σ : ℝ) :
      actualPrimal ((P2.G P2.zetaA)-1) (p2Lift P2.zetaA) n σ=
        P2.reducedSlack P2.zetaA n σ/lagDenominator (P2.G P2.zetaA) n := by
    rw [actualPrimal_eq_raw_div hh _ hn,p2Lift_rawBranch P2.zetaA_mem P2.zeta1_lt_zetaA.le n hn σ]
    rw [show 1+((P2.G P2.zetaA)-1)=(P2.G P2.zetaA) by ring]
  have hL : actualPrimal ((P2.G P2.zetaA)-1) (p2Lift P2.zetaA) 1 (-1)=0 := by
    rw [hp 1 (by omega),P2.lower1_zero P2.zetaA_mem,zero_div]
  have hU2 : actualPrimal ((P2.G P2.zetaA)-1) (p2Lift P2.zetaA) 2 1=0 := by
    rw [hp 2 (by omega),P2.upper2_zero P2.zetaA_mem,zero_div]
  have hU3 : actualPrimal ((P2.G P2.zetaA)-1) (p2Lift P2.zetaA) 3 1=0 := by
    rw [hp 3 (by omega),P2.upper3_zero P2.zetaA_mem,zero_div]
  have hU5 : actualPrimal ((P2.G P2.zetaA)-1) (p2Lift P2.zetaA) 5 1=0 := by
    rw [hp 5 (by omega),P2.upper5_factor P2.zetaA_mem,P2.N12_zetaA,zero_mul,zero_div]
  obtain ⟨h0,h1,h2,h3⟩ := regularSystem_primal_exact hh (p2Lift P2.zetaA)
  rw [hL,mul_zero] at h0
  rw [hU2,mul_zero] at h1
  rw [hU3,mul_zero] at h2
  rw [hU5,mul_zero] at h3
  obtain ⟨h4,h5,h6⟩ := p2Lift_dual_equations P2.zetaA_mem
  have z0 := (mul_eq_zero.mp h0).resolve_left hh0
  have z1 := (mul_eq_zero.mp h1).resolve_left hh0
  have z2 := (mul_eq_zero.mp h2).resolve_left hh0
  have z3 := (mul_eq_zero.mp h3).resolve_left hh0
  ext i
  fin_cases i
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact h4
  · exact h5
  · exact h6

end polyak.Boundary.P5
