import krylov.Reference.GradientMeasure
import krylov.Reference.MomentDeterminant

/-!
Article: main_krylov, s2:eq:cg and lem:chris, exhaustion and zero minimum.
Use: complete the finite-support Christoffel dictionary at and beyond the
actual atom count, while keeping uniqueness statements in their valid degree range.
Source: finite polynomial interpolation, the proved Gram projection and actual CG stopping.
-/

namespace krylov.Reference
noncomputable section
open Polynomial Matrix jacobi.Finite
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator

/-- At the support size the constructed moment polynomial has exactly zero actual spectral L² error.
Use: supplies the attaining terminal Christoffel polynomial, including its genuine normalization.
Article: main_krylov, lem:chris, λ_N(0;ν)=0.
Proof: the N positive shifted monomials form a full basis, so their actual
orthogonal Schur residual is orthogonal to the entire ambient space and vanishes. -/
theorem momentPolynomial_exhausts {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i) :
    M.evaluate (momentPolynomial M N)=0 := by
  -- Full span is proved from the true positive-node Vandermonde independence and the actual dimension.
  have hli := shiftedMonomials_independent M hn (le_refl N)
  have hspan : Submodule.span ℝ (Set.range (shiftedMonomials M N))=⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli]; simp)
  let r := Gram.residual (shiftedMonomials M N) (M.evaluate 1)
  have hle : Submodule.span ℝ (Set.range (shiftedMonomials M N))≤(innerSL ℝ r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ r (shiftedMonomials M N i)=0
    rw [real_inner_comm]
    exact Gram.residual_orthogonal hli _ i
  have ho : inner ℝ r r=0 := hle (by rw [hspan]; trivial)
  rw [evaluate_momentPolynomial]
  exact inner_self_eq_zero.mp ho

/-- At degree N the normalized zero-error polynomial is unique.
Use: terminal uniqueness is justified even though ordinary evaluation is no longer injective at degree N.
Article: main_krylov, lem:chris, normalized terminal polynomial.
Proof: the normalized difference is Xq of degree below N; positive nodes and
zero weighted evaluation make q vanish at all N distinct atoms, hence q is zero. -/
theorem momentPolynomial_terminal_unique {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i)
    {p : ℝ[X]} (hp : p.natDegree≤N) (h0 : p.eval 0=1) (hz : M.evaluate p=0) :
    p=momentPolynomial M N := by
  -- Dividing the normalized difference, rather than the competitor itself, preserves the strict root-counting degree bound.
  have ha := momentPolynomial_admissible M N
  obtain ⟨q, he, hq⟩ := normalized_difference hp ha.1 (h0.trans ha.2.symm)
  have hnodes (r : ℝ[X]) (hr : M.evaluate r=0) (i : Fin N) : r.eval (M.node i)=0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) hr
    change Real.sqrt (M.weight i)*r.eval (M.node i)=0 at hc
    exact (mul_eq_zero.mp hc).resolve_left (Real.sqrt_pos.mpr (M.positive i)).ne'
  have hzero : q=0 := by
    by_cases hq0 : q=0
    · exact hq0
    · apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q M.distinct
      · intro i
        have hv := congrArg (fun r : ℝ[X] => r.eval (M.node i)) he
        rw [eval_sub, eval_mul, eval_X, hnodes p hz i,
          hnodes (momentPolynomial M N) (momentPolynomial_exhausts M hn) i, sub_self] at hv
        exact (mul_eq_zero.mp hv.symm).resolve_left (hn i).ne'
      · simpa only [Fintype.card_fin] using (natDegree_lt_iff_degree_lt hq0).mpr (mem_degreeLT.mp hq)
  rw [hzero, mul_zero] at he
  exact sub_eq_zero.mp he

/-- The exterior Christoffel value, extended by its actual zero minimum after all atoms have been exhausted.
Use: states the energy dictionary for every iteration, with no undefined kernel reciprocal at terminal degrees.
Article: main_krylov, s2:eq:cg and lem:chris, λ_m(0;ν). -/
def finiteChristoffelValue {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) : ℝ :=
  if m<N then (christoffelKernel M m 0)⁻¹ else 0

/-- The finite-support Christoffel value is attained and is the actual minimum over every admissible degree.
Use: the zero terminal and post-terminal regimes are included in the same actual minimization statement.
Article: main_krylov, s2:eq:cg, λ_m=min∫p²dν with p(0)=1.
Proof: before exhaustion use the constructed normalized kernel; afterward
use the constructed normalized zero-error degree-N moment polynomial. -/
theorem finiteChristoffel_minimum {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i) (m : ℕ) :
    (∃ p : ℝ[X], p.natDegree≤m ∧ p.eval 0=1 ∧ ‖M.evaluate p‖^2=finiteChristoffelValue M m) ∧
      ∀ p : ℝ[X], p.natDegree≤m → p.eval 0=1 → finiteChristoffelValue M m≤‖M.evaluate p‖^2 := by
  -- The post-exhaustion optimizer has degree N and therefore stays admissible at every later requested degree.
  by_cases hm : m<N
  · rw [finiteChristoffelValue, ite_eq_left hm]
    refine ⟨⟨christoffelPolynomial M m 0, (christoffelPolynomial_admissible M m 0).1,
      (christoffelPolynomial_admissible M m 0).2, christoffelPolynomial_norm M hm 0⟩, ?_⟩
    exact fun p hp h0 => (christoffel_minimum_unique M hm 0 hp h0).1
  · rw [finiteChristoffelValue, ite_eq_right hm]
    refine ⟨⟨momentPolynomial M N, (momentPolynomial_admissible M N).1.trans (by omega),
      (momentPolynomial_admissible M N).2, ?_⟩, fun p _ _ => sq_nonneg _⟩
    rw [momentPolynomial_exhausts M hn, norm_zero, zero_pow (by omega : 2≠0)]

/-- The terminal moment determinant ratio is zero, with a genuinely positive denominator.
Use: completes the printed determinant formula at m=N.
Article: main_krylov, lem:chris, det H⁽⁰⁾_(N+1)/det H⁽²⁾_N=0.
Proof: the actual Schur residual is zero at exhaustion, so the already proved augmented determinant identity has zero complement. -/
theorem terminal_moment_determinant {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i) :
    (augmentedGram (shiftedMonomials M N) (M.evaluate 1)).det/(Matrix.gram ℝ (shiftedMonomials M N)).det=0 := by
  have hli := shiftedMonomials_independent M hn (le_refl N)
  have hc : Gram.complement (shiftedMonomials M N) (M.evaluate 1)=0 := by
    rw [← Gram.residual_norm_sq hli, ← evaluate_momentPolynomial, momentPolynomial_exhausts M hn,
      norm_zero, zero_pow (by omega : 2≠0)]
  rw [augmentedGram_det hli, hc, mul_zero, zero_div]

/-- The terminal zero-error polynomial is the normalized full characteristic continuant of the actual reconstructed matrix.
Use: the determinant representation remains valid exactly at the support size.
Article: main_krylov, prop:dict(i) and lem:chris, terminal normalized determinant.
Proof: the actual characteristic polynomial is the product over the given
positive nodes; its normalization is nonzero at zero and vanishes at every node,
so the proved normalized terminal interpolation uniqueness applies. -/
theorem momentPolynomial_leading {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i) :
    momentPolynomial M N=C ((M.reconstructed.data.leading N).eval 0)⁻¹*M.reconstructed.data.leading N := by
  -- The terminal polynomial and all its denominators are obtained from the actual prescribed support.
  let P := M.reconstructed.data.leading N
  have hchar : P=∏ i, (X-C (M.node i)) :=
    (M.reconstructed.data.block_eq_charpoly M.reconstructed.coupling_nonneg 0 N).trans M.reconstructed_charpoly
  have h0 : P.eval 0≠0 := by
    rw [hchar, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa only [eval_sub, eval_X, eval_C, zero_sub] using neg_ne_zero.mpr (hn i).ne'
  change (M.reconstructed.data.leading N).eval 0≠0 at h0
  have hnodes (i : Fin N) : P.eval (M.node i)=0 := by
    rw [hchar, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [eval_sub, eval_X, eval_C, sub_self])
  apply Eq.symm
  apply momentPolynomial_terminal_unique M hn
  · exact (natDegree_C_mul_le _ _).trans (le_of_eq (M.reconstructed.data.block_natDegree M.reconstructed.coupling_nonneg 0 N))
  · simp only [eval_mul, eval_C, inv_mul_cancel₀ h0]
  · ext i
    change Real.sqrt (M.weight i)*(C (P.eval 0)⁻¹*P).eval (M.node i)=0
    rw [eval_mul, eval_C, hnodes, mul_zero, mul_zero]

/-- The actual CG residual has its actual normalized Jacobi determinant representation up to and including exact termination.
Use: the full-support Gaussian rule has the same proved actual terminal residual as CG.
Article: main_krylov, prop:dict(i), residual determinant formula at every defined CG degree.
Proof: use the established pre-exhaustion orthogonal-polynomial identity;
at exhaustion the true zero gradient makes its actual gradient-measure evaluation zero,
and the proved terminal interpolation theorem identifies the normalized characteristic polynomial. -/
theorem residualPolynomial_leading_le {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ} (hm : m≤referenceAtomCount base hb g) :
    let J := (gradientSpectralData base hb g hg).reconstructed
    CG.residualPolynomial (cgOperator base) g m=C ((J.data.leading m).eval 0)⁻¹*J.data.leading m := by
  -- At the terminal degree, solve the actual interpolation problem rather than assuming an extra degree-N orthogonal polynomial.
  by_cases hlt : m<referenceAtomCount base hb g
  · exact residualPolynomial_leading base hb g hg hlt
  · have heq : m=referenceAtomCount base hb g := by omega
    let M := gradientSpectralData base hb g hg
    let r := CG.residualPolynomial (cgOperator base) g m
    have hz : CG.gradient (cgOperator base) g m=0 := (cg_stopping_iff base hb g m).mpr (by omega)
    have he := gradientSpectralData_inner base hb g hg r r
    rw [(CG.polynomialAction_pair (cgOperator base) g m).1, hz, inner_zero_left] at he
    have heval : M.evaluate r=0 := inner_self_eq_zero.mp
      ((mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)))
    have hn (i) : 0<M.node i := vectorSpectralData_node_pos base hb g hg i
    have hd : r.natDegree≤(activeSpectralValues base hb.1 g).card := by
      rw [gradientSpectralData_count base hb g, ← heq]
      exact (CG.polynomial_degree (cgOperator base) g m).1
    have hi := momentPolynomial_terminal_unique M hn hd (CG.residualPolynomial_zero (cgOperator base) g m) heval
    rw [momentPolynomial_leading M hn] at hi
    dsimp only
    simpa only [M, r, gradientSpectralData_count base hb g, ← heq] using hi

/-- The actual CG/Christoffel energy identity holds at every time, including the solved tail.
Use: later statements may use finite stopping without adding an unstated degree restriction.
Article: main_krylov, s2:eq:cg and lem:chris, the complete energy profile.
Proof: before exhaustion use the proved kernel identity; at and after the actual atom count, the proved zero-preserving CG stopping rule gives both sides zero. -/
theorem cg_energy_christoffel_all {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (m : ℕ) :
    ‖cgCanonicalError base g m‖^2=‖cgCanonicalError base g 0‖^2*
      finiteChristoffelValue (energySpectralData base hb g hg) m := by
  by_cases hm : m<referenceAtomCount base hb g
  · rw [finiteChristoffelValue, ite_eq_left hm]
    exact cg_energy_christoffel base hb g hg hm
  · have hz := CG.gradient_eq_zero_of_le (cgOperator base) g (cg_terminates base hb g) (by omega : referenceAtomCount base hb g≤m)
    rw [finiteChristoffelValue, ite_eq_right hm, mul_zero]
    simp only [cgCanonicalError, hz, map_zero, norm_zero, zero_pow (by omega : 2≠0)]

end
end krylov.Reference
