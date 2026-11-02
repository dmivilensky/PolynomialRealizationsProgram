import jacobi.Applications.ClosedEndpoint

/-!
Polynomial fibres with nonnegative Jacobi links, allowing repeated roots
and the left endpoint minus one. The shared Jacobi record already permits
zero links; only the older irreducibility predicate has to be dropped.
Use: AllThreeTerm applies the endpoint energy identity to every restart
pattern, rather than only to a Jacobi block with simple interior spectrum.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
Article role: the full nonnegative-link fibre, prefix exactness and the restart criterion.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix

/-- Membership in the full nonnegative-link fibre. Nonnegative links are
already part of `Jacobi`; the terminal characteristic polynomial is the
only additional condition.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
def InClosedFiber {N : ℕ} (J : Jacobi N) (p : ℝ[X]) : Prop := J.matrix.charpoly=p

/-- The full fibre retains every reducible chain and every placement of
its blocks. It imposes no endpoint spectral weights.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
abbrev ClosedFiber (N : ℕ) (p : ℝ[X]) := {J : Jacobi N // InClosedFiber J p}

/-- A descending root list counted with multiplicity. The right endpoint
is excluded because the endpoint normalization and Green inverse need it.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
structure ClosedNodes (N : ℕ) where
  /-- Roots may coincide.
  Article: jacobi, Lemma 5.2 and Theorem 5.3.
  -/
  value : Fin N → ℝ
  /-- The root list uses the same descending convention as the simple fibre.
  Article: jacobi, Lemma 5.2 and Theorem 5.3.
  -/
  antitone : Antitone value
  /-- Minus one is permitted, while one is excluded.
  Article: jacobi, Lemma 5.2 and Theorem 5.3.
  -/
  interval : ∀ i,value i∈Set.Ico (-1) 1

namespace ClosedNodes
variable {N : ℕ} (S : ClosedNodes N)

/-- The actual monic polynomial, retaining every repeated endpoint root.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
def polynomial : ℝ[X] := ∏ i,(X-C (S.value i))

/-- Every terminal factor is strictly positive at the normalization point.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem endpoint_pos : 0<S.polynomial.eval 1 := by
  simp only [polynomial,eval_prod,eval_sub,eval_X,eval_C]
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (S.interval i).2)

/-- Characteristic roots identify the spectrum without a simplicity or
irreducibility premise. Repeated roots are retained in the polynomial.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem spectrum_eq {J : Jacobi N} (hJ : InClosedFiber J S.polynomial) :
    spectrum ℝ J.matrix=Set.range S.value := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,hJ]
  simp only [Polynomial.IsRoot,polynomial,eval_prod,eval_sub,eval_X,eval_C,
    Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero,Set.mem_range]
  constructor <;> rintro ⟨i,hi⟩ <;> exact ⟨i,hi.symm⟩

/-- Every closed-fibre member has a positive endpoint pencil, including
matrices whose spectrum contains minus one with arbitrary multiplicity.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem endpoint_posDef {J : Jacobi N} (hJ : InClosedFiber J S.polynomial) :
    (1-J.matrix).PosDef := by
  have h := J.affine_posDef 1 (-1) (fun x hx => by
    rw [S.spectrum_eq hJ] at hx
    obtain ⟨i,rfl⟩ := hx
    linarith [(S.interval i).2])
  simpa [Matrix.scalar,sub_eq_add_neg] using h

/-- All actual prefix denominators are positive even when a preceding
coupling vanishes. This is the only denominator input to the exact recurrence.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem prefix_pos {J : Jacobi N} (hJ : InClosedFiber J S.polynomial)
    {n : ℕ} (hn : n≤N) : 0<(J.data.leading n).eval 1 :=
  Applications.endpoint_prefix_pos_of_posDef (S.endpoint_posDef hJ) hn

/-- The original prefix-exact realization survives every allowed restart.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem prefix_exact {J : Jacobi N} (hJ : InClosedFiber J S.polynomial)
    (n : ℕ) (hn : n≤N) :
    (Applications.endpointMethod J).realization.residualPolynomial n=
      Applications.endpointResidual J n :=
  Applications.endpoint_prefix_exact_of_posDef (S.endpoint_posDef hJ) n hn

/-- The actual zero-endpoint channel is exactly four times the full
resolvent energy for every closed-fibre member, with no extra contribution
at a restart. Singleton blocks contribute their own diagonal squares.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem endpoint_gain_square {J : Jacobi N} (hJ : InClosedFiber J S.polynomial) :
    ((Applications.endpointMethod J).realization.kernelNorm N 0 0)^2=4*J.energy := by
  have he : 0≤J.energy := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Applications.endpoint_gain_energy_of_posDef (S.endpoint_posDef hJ),mul_pow,
    Real.sq_sqrt he]
  norm_num

/-- A vanished squared link is exactly a vanished momentum coefficient.
This identifies the matrix's block separation with the iteration's restart.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem restart_iff {J : Jacobi N} (hJ : InClosedFiber J S.polynomial)
    {i : ℕ} (hi : i<N) :
    (Applications.endpointMethod J).b i=0 ↔ J.data.aSq i=0 := by
  have hp := (S.prefix_pos hJ (show i-1≤N by omega)).ne'
  have hq := (S.prefix_pos hJ (show i+1≤N by omega)).ne'
  simp only [Applications.endpointMethod,neg_eq_zero,div_eq_zero_iff,mul_eq_zero,
    hp,hq,or_false]

end ClosedNodes

/-- Every older irreducible fibre is contained in the full fibre without
changing its characteristic polynomial or its energy.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem InFiber.closed {N : ℕ} {J : Jacobi N} {p : ℝ[X]} (hJ : InFiber J p) :
    InClosedFiber J p := hJ.2

end
end jacobi.Finite
