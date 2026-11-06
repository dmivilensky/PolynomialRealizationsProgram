import nesterov.Faithful.TwoScale

/-! Smoothness and frequency evenness of the literal two-scale symbol. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

def linearPolynomial (c ε : ℝ) : Polynomial ℝ :=
  circleProductPolynomial (F.memory+2) (familyA F ε) (familyB F ε) (1-c*ε)

theorem linearPolynomial_eval (c ε ω : ℝ) :
    (linearPolynomial F c ε).eval (1-Real.cos ω)=linearSymbol F c ε ω := by
  rw [linearPolynomial,circleProductPolynomial_eval _ _ _ _ (familyA_natDegree F ε) (familyB_natDegree F ε)]
  unfold familyA familyB linearSymbol evalComplex linearCircle
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X,Polynomial.map_C,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C,
    StationaryMethod.characteristic_eq_polynomial_eval,Complex.ofReal_one,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,one_mul]
  congr 1
  let z := linearCircle c ε ω
  let U := evalComplex (F.u ε) z
  let V := evalComplex (F.v ε) z
  let m : ℂ := (ε^2:ℝ)
  change (1-z)*(m*U-V)*star (U-V)=(1-z)*(V-m*U)*star (V-U)
  rw [show U-V= -(V-U) by ring,star_neg]
  ring

theorem linearSymbol_even (c ε ω : ℝ) : linearSymbol F c ε (-ω)=linearSymbol F c ε ω := by
  simp_rw [←linearPolynomial_eval,Real.cos_neg]

theorem linearPolynomial_coeff_ck {k : ℕ} (hc : F.CoeffCk k) (c : ℝ) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(linearPolynomial F c ε).coeff j) (Ici 0) 0 := by
  apply circleProductPolynomial_coeff_ck (familyA_coeff_ck F hc) (familyB_coeff_ck F hc)
  exact contDiffWithinAt_const.sub (contDiffWithinAt_const.mul contDiffWithinAt_id)

/-- The endpoint germ of H is C^k on the actual domain ε≥0. -/
theorem linearSymbol_contDiffWithinAt {k : ℕ} (hc : F.CoeffCk k) (c : ℝ) :
    ContDiffWithinAt ℝ k (fun p : ℝ × ℝ=>linearSymbol F c p.1 p.2)
      {p | 0≤p.1} (0,0) := by
  let N := 2*(F.memory+2)+1
  have heval (p : ℝ × ℝ) : linearSymbol F c p.1 p.2=
      ∑ j∈Finset.range N,(linearPolynomial F c p.1).coeff j*(1-Real.cos p.2)^j := by
    rw [←linearPolynomial_eval]
    have hd : (linearPolynomial F c p.1).natDegree<N := (circleProductPolynomial_natDegree_le
      (F.memory+2) (familyA F p.1) (familyB F p.1) (1-c*p.1)).trans_lt (by dsimp [N];omega)
    exact Polynomial.eval_eq_sum_range' hd _
  simp_rw [heval]
  apply ContDiffWithinAt.sum
  intro j hj
  apply ContDiffWithinAt.mul
  · convert! (linearPolynomial_coeff_ck F hc c j).comp ((0:ℝ),(0:ℝ))
      contDiffWithinAt_fst (fun p hp=>hp)
  · exact (contDiffWithinAt_const.sub (contDiffWithinAt_snd.cos)).pow j


/-- Literal joint-neighborhood form of the source expansion. -/
theorem two_scale_at_origin (c : ℝ) :
    (fun p : ℝ × ℝ=>linearSymbol F c p.1 p.2-
      p.1/y*(c*Flow.delta θ y c*p.1^2+(θ-3*c)*p.2^2))=o[𝓝[{p | 0<p.1}] ((0:ℝ),(0:ℝ))]
      (fun p=>(p.1+|p.2|)^3) := by
  apply two_scale_expansion F
  · apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · exact self_mem_nhdsWithin
  · exact continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end
end nesterov.Faithful
