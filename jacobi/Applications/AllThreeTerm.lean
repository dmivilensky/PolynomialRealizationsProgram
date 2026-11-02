import jacobi.Applications.NesterovClosedSpectrum
import jacobi.Applications.TerminalRealization
import jacobi.Finite.OrderedSpectrum
import jacobi.Finite.ClosedMinimum

/-!
The full closed-fibre Nesterov lower bound and its attained finite minima.
All spectra are the actual repeated-root spectra of the full polynomial.
The endpoint recurrence is identified with the original residual, and the
quarter-edge transfer retains every admissible nonnegative-link matrix.
Use: NesterovComparisons assembles the optimal endpoint gain comparison;
PaddedBlocks supplies concrete matching competitors at the symmetric order.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
Article role: the exact full residual, attained normalized endpoint minimum and all-realization
lower bound.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set Polynomial chebyshev2
open jacobi.Jacobi jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized minimum of the endpoint channel on a complete
closed fibre. The factor four is the proved exact Green-energy identity.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
def closedEndpointMinimum {N : ℕ} (S : ClosedNodes N) : ℝ≥0∞ :=
  4*closedFibreEnergyInfimum S

/-- The endpoint minimum is attained, and equals the literal squared
channel divided by the full cubic horizon. Thus the subsequent lower
bound concerns an actual minimum over all restart patterns.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem closedEndpointMinimum_attained {N : ℕ} (S : ClosedNodes N) :
    ∃ J : Jacobi N,InClosedFiber J S.polynomial ∧
      closedEndpointMinimum S=ENNReal.ofReal
        (((endpointMethod J).realization.kernelNorm N 0 0)^2/(N:ℝ)^3) ∧
      ∀ K : Jacobi N,InClosedFiber K S.polynomial →
        ((endpointMethod J).realization.kernelNorm N 0 0)^2≤
          ((endpointMethod K).realization.kernelNorm N 0 0)^2 := by
  obtain ⟨J,hJ,hmin⟩ := S.exists_minimizer
  have hcost : closedFibreEnergyInfimum S=fibreCost J := by
    refine le_antisymm ?_ ?_
    · exact sInf_le ⟨J,hJ,rfl⟩
    apply le_sInf
    rintro _ ⟨K,hK,rfl⟩
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hmin K hK) (by positivity))
  refine ⟨J,hJ,?_,fun K hK => ?_⟩
  · rw [closedEndpointMinimum,hcost,S.endpoint_gain_square hJ,fibreCost]
    calc
      (4:ℝ≥0∞)*ENNReal.ofReal (J.energy/(N:ℝ)^3)=
          ENNReal.ofReal (4*(J.energy/(N:ℝ)^3)) := by
        simpa only [ENNReal.ofReal_ofNat] using
          (ENNReal.ofReal_mul (q := J.energy/(N:ℝ)^3) (by norm_num : (0:ℝ)≤4)).symm
      _=ENNReal.ofReal (4*J.energy/(N:ℝ)^3) := by congr 1; ring
  · rw [S.endpoint_gain_square hJ,S.endpoint_gain_square hK]
    exact mul_le_mul_of_nonneg_left (hmin K hK) (by norm_num)

/-- Every closed-fibre endpoint method has precisely the original
Nesterov residual, including its repeated Landweber factor.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem padded_endpoint_terminal {b : ℝ} (hb : -1<b) (e m : ℕ)
    {J : Jacobi (nesterovParityDimension e m)}
    (hJ : InClosedFiber J (nesterovParityNodes (b/2) (by linarith) e m).polynomial) :
    (endpointMethod J).realization.residualPolynomial (nesterovParityDimension e m)=
      nesterovResidual b m e := by
  let S := nodes (b/2) ((e:ℝ)-1/2) (by linarith : -1<b/2)
    (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2) m
  rw [(nesterovParityNodes (b/2) (by linarith) e m).prefix_exact hJ _ le_rfl]
  have hp : J.data.leading (nesterovParityDimension e m)=
      S.polynomial*(X+1)^(m+1+e) := by
    rw [chebyshev1.JacobiData.leading,J.data.block_eq_charpoly J.coupling_nonneg]
    change J.matrix.charpoly=_
    rw [hJ]
    exact S.padMinusOne_polynomial _
  apply Polynomial.funext
  intro t
  rw [endpointResidual_eval,hp,nesterovResidual,nesterovFactor]
  simp only [eval_mul,eval_pow,eval_sub,eval_one,eval_X,eval_add]
  rw [shiftedPolynomial_product (by linarith : -1<b/2)
      (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2) m]
  have hfactor : S.polynomial.eval (1-2*t)/S.polynomial.eval 1=
      ∏ i : Fin m,(1-t/shiftedRoots (b/2) ((e:ℝ)-1/2) (by linarith)
        (by linarith [Nat.cast_nonneg (α := ℝ) e]) m i) := by
    simp only [S,Nodes.polynomial,eval_prod,eval_sub,eval_X,eval_C,nodes]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hi := (shiftedRoots_properties (by linarith : -1<b/2)
      (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2) i).2.1.ne'
    let r := shiftedRoots (b/2) ((e:ℝ)-1/2) (by linarith)
      (by linarith [Nat.cast_nonneg (α := ℝ) e]) m i
    change ((1-2*t)-(1-2*r))/(1-(1-2*r))=1-t/r
    have hr : r≠0 := hi
    field_simp [hr]
    ring
  rw [← hfactor]
  have hS : S.polynomial.eval 1≠0 := S.endpoint_pos.ne'
  have hpow : (1-2*t+1)^(m+1+e)=2^(m+1+e)*(1-t)^(m+1+e) := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hpow]
  norm_num only [show (1:ℝ)+1=2 by norm_num]
  field_simp



/-- A repeated endpoint root forces a restart: no positive-link Jacobi
chain can realize this full polynomial, since its spectrum is simple.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem nesterov_restarts_necessary {a : ℝ} (ha : -1<a) (e m : ℕ)
    (hL : 2≤m+1+e) :
    ¬∃ J : Jacobi (nesterovParityDimension e m),
      InFiber J (nesterovParityNodes a ha e m).polynomial := by
  rintro ⟨J,hJ⟩
  have hp : J.matrix.charpoly=
      (nodes a ((e:ℝ)-1/2) ha (by linarith [Nat.cast_nonneg (α := ℝ) e]) m).polynomial*
        (X+1)^(m+1+e) := hJ.2.trans (Nodes.padMinusOne_polynomial _ _)
  generalize hindex : m+1+e=L at hp hL
  have h0 : L≠0 := by omega
  have h1 : L-1≠0 := by omega
  have hs : (-1:ℝ)∈spectrum ℝ J.matrix := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    simp only [Polynomial.IsRoot,hp,eval_mul,eval_pow,eval_add,eval_X,eval_one,
      neg_add_cancel,zero_pow h0,mul_zero]
  apply charpoly_derivative_ne_spectrum J hJ.1 hs
  rw [hp,derivative_mul,derivative_pow]
  simp only [eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,
    neg_add_cancel,zero_pow h0,zero_pow h1,mul_zero,zero_mul,zero_add]

/-- Dimension transport of a Jacobi chain preserves its actual finite
coefficients, with only the ambient finite index type transported.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
def castJacobi {N M : ℕ} (h : N=M) (J : Jacobi N) : Jacobi M := h ▸ J

/-- Characteristic polynomials are unchanged by exact dimension transport.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem castJacobi_charpoly {N M : ℕ} (h : N=M) (J : Jacobi N) :
    (castJacobi h J).matrix.charpoly=J.matrix.charpoly := by
  subst M
  rfl

/-- The actual recurrence polynomials are unchanged by dimension transport.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem castJacobi_residual {N M : ℕ} (h : N=M) (J : Jacobi N) (k : ℕ) :
    (endpointMethod (castJacobi h J)).realization.residualPolynomial k=
      (endpointMethod J).realization.residualPolynomial k := by
  subst M
  rfl

/-- The prescribed terminal polynomial is unchanged by dimension transport.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem castClosedNodes_polynomial {N M : ℕ} (h : N=M) (S : ClosedNodes N) :
    (castClosedNodes h S).polynomial=S.polynomial := by
  subst M
  rfl

/-- Every actual full-horizon closed-fibre method has the original
Nesterov residual at that same horizon. This includes all restarts,
all interleavings and both parities, without a dimension-conversion premise.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem nesterov_closed_terminal {b : ℝ} (hb : -1<b) (n : ℕ) {J : Jacobi (n+1)}
    (hJ : InClosedFiber J (nesterovClosedNodes (b/2) (by linarith) n).polynomial) :
    (endpointMethod J).realization.residualPolynomial (n+1)=nesterovAt b (n+1) := by
  have hdim : nesterovParityDimension (n%2) (n/2)=n+1 := by
    unfold nesterovParityDimension
    omega
  let K := castJacobi hdim.symm J
  have hK : InClosedFiber K (nesterovParityNodes (b/2) (by linarith) (n%2) (n/2)).polynomial := by
    rw [InClosedFiber,castJacobi_charpoly]
    change J.matrix.charpoly=(castClosedNodes hdim
      (nesterovParityNodes (b/2) (by linarith) (n%2) (n/2))).polynomial at hJ
    rwa [castClosedNodes_polynomial] at hJ
  have h := padded_endpoint_terminal hb (n%2) (n/2) hK
  rw [castJacobi_residual,hdim] at h
  simpa only [nesterovAt,Nat.add_sub_cancel] using h

/-- The full closed Nesterov fibre satisfies the exact one-eighth
homogeneous continuum lower bound, without a spectral convergence premise.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem nesterov_closed_energy_lower {a : ℝ} (ha : -1<a) :
    (1/8:ℝ≥0∞)*homogeneousLowerConstant (jacobi.Bessel.edgeSpectrum a ha)≤
      liminf (fun n : ℕ => closedFibreEnergyInfimum (nesterovClosedNodes a ha n)) atTop :=
  closed_quarter_lowerConstant_transfer (fun n => n+1) (nesterovClosedNodes a ha)
    (fun n => Nat.succ_pos n) (tendsto_add_atTop_nat 1)
    (jacobi.Bessel.edgeSpectrum a ha) (nesterovClosed_spectral_limit ha)

/-- All three-term realizations, with the printed endpoint factor one
half. The finite minima are attained over the entire closed fibre.
Article: jacobi, Theorem 5.3 and Lemma 5.2.
-/
theorem nesterov_all_three_term_lower {b : ℝ} (hb : -1<b) :
    (1/2:ℝ≥0∞)*homogeneousLowerConstant
      (jacobi.Bessel.edgeSpectrum (b/2) (by linarith))≤
      liminf (fun n : ℕ => closedEndpointMinimum
        (nesterovClosedNodes (b/2) (by linarith) n)) atTop := by
  have h := mul_le_mul_of_nonneg_left
    (nesterov_closed_energy_lower (by linarith : -1<b/2)) (show (0:ℝ≥0∞)≤4 from bot_le)
  have he : (4:ℝ≥0∞)*((1/8:ℝ≥0∞)*homogeneousLowerConstant
      (jacobi.Bessel.edgeSpectrum (b/2) (by linarith)))=
      (1/2:ℝ≥0∞)*homogeneousLowerConstant
        (jacobi.Bessel.edgeSpectrum (b/2) (by linarith)) := by
    rw [← mul_assoc]
    congr 1
    have hq : (4:ℝ≥0∞)*(8:ℝ≥0∞)⁻¹=(2:ℝ≥0∞)⁻¹ := by
      rw [show (8:ℝ≥0∞)=4*2 by norm_num,ENNReal.mul_inv (by left; norm_num) (by left; norm_num),← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num : (4:ℝ≥0∞)≠0) (by norm_num : (4:ℝ≥0∞)≠∞),one_mul]
    simpa only [one_div,one_mul] using hq
  rw [he] at h
  exact h.trans (by
    simpa only [Pi.mul_apply,Pi.mul_def,closedEndpointMinimum,liminf_const] using
      (ENNReal.le_liminf_mul (u := fun _ : ℕ => (4:ℝ≥0∞))
        (v := fun n => closedFibreEnergyInfimum (nesterovClosedNodes (b/2) (by linarith) n))
        (f := atTop)))

end
end jacobi.Applications
