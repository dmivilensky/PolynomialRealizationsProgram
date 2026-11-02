import jacobi.Finite.ComplexResolvent
import jacobi.Analytic.FiniteShiftedProfiles

/-!
Article: jacobi, Corollary C.6.
The actual complex shifted inverse of the original target matrix is
identified exactly with its genuine finite shifted diagonal spectral
sum, at every shift with the proved actual finite nonzero denominators.
This is an algebraic identity, not a definition by spectral approximation.
Use: shiftedTargetResolvent is the literal original complex inverse.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter Matrix jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology

/-- The article's actual edge-scaled complex spectral point at the
true matrix dimension N=n+1.
Use: shiftedTargetResolvent is the literal original complex inverse.
Article: jacobi, Corollary C.6.
-/
def edgePoint (n:ℕ) (w:ℂ) : ℂ := 1+w/(2*(((n:ℝ)+1:ℝ):ℂ)^2)

/-- The actual original complex matrix resolvent at its genuine edge point.
Use: Theorem C.5's finite bounds and limits refer to this literal matrix
inverse, identified with the independently proved finite spectral sums.
Article: jacobi, Corollary C.6.
-/
def shiftedTargetResolvent (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (w:ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (edgePoint n w • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
    (targetChain a b ha hb n).matrix.map Complex.ofRealHom)⁻¹

/-- The original finite transformed denominator is exactly the true
complex spectral gap divided by its original positive unshifted gap.
Use: shiftedTarget_gap_ne and shifted finite matrix identification
retain the same actual matrix dimension and spectral point.
Article: jacobi, Corollary C.6.
Proof: insert the genuine original reciprocal-node formula and cancel
the actual nonzero spectral gap and positive true matrix dimension. -/
theorem finite_denominator_gap (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) (w:ℂ) :
    1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k.val/2:ℝ):ℂ)*w=
      (edgePoint n w-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ))/
        (1-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ)) := by
  rw [jacobi.Jacobi.finiteLambdaAt_eq ha hb k.isLt,jacobi.Jacobi.finiteLambda_node ha hb k]
  have hgap : (1:ℂ)-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ)≠0 := by
    exact_mod_cast (sub_pos.mpr ((jacobi.Jacobi.nodes a b ha hb (n+1)).interval k).2).ne'
  have hN : (((n:ℝ)+1:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  unfold edgePoint
  push_cast
  field_simp
  ring

/-- The actual finite complex spectral gaps are nonzero whenever the
same original reciprocal-coordinate denominators are nonzero.
Use: the actual finite compact denominator theorem discharges every
matrix pole-exclusion premise in all original conclusions of D.
Article: jacobi, Corollary C.6.
Proof: a vanishing actual spectral gap would make the proved exact
original denominator-gap quotient vanish. -/
theorem shiftedTarget_gap_ne (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (w:ℂ)
    (hden:∀k:ℕ,1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2:ℝ):ℂ)*w≠0)
    (k:Fin (n+1)) : edgePoint n w-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ)≠0 := by
  intro hz
  apply hden k.val
  rw [finite_denominator_gap,hz,zero_div]

/-- The true original padded finite shifted coefficient is exactly
its original normalized actual complex spectral reciprocal.
Use: finiteShiftedDiagonal_matrix identifies the genuine finite
spectral sums with the actual original complex matrix inverse.
Article: jacobi, Corollary C.6.
Proof: use the true original reciprocal-node formula and exact
denominator-gap quotient, whose actual nonzero gaps are proved. -/
theorem finiteShiftedEdge_gap (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (w:ℂ)
    (hden:∀k:ℕ,1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2:ℝ):ℂ)*w≠0)
    (k:Fin (n+1)) : finiteShiftedEdge a b ha hb n k.val w=
      1/((((n:ℝ)+1:ℝ):ℂ)^2*(edgePoint n w-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ))) := by
  unfold finiteShiftedEdge resolventTransform
  rw [finite_denominator_gap,jacobi.Jacobi.finiteLambdaAt_eq ha hb k.isLt,jacobi.Jacobi.finiteLambda_node ha hb k]
  have hgap := shiftedTarget_gap_ne a b ha hb n w hden k
  have hbase : (1:ℂ)-((jacobi.Jacobi.nodes a b ha hb (n+1)).value k:ℂ)≠0 := by
    exact_mod_cast (sub_pos.mpr ((jacobi.Jacobi.nodes a b ha hb (n+1)).interval k).2).ne'
  push_cast
  field_simp

/-- The genuine shifted finite diagonal spectral sum equals the actual
original shifted complex matrix inverse in its printed physical scale.
Use: the uniform finite profile and both energy limits now concern
the original resolvent of Theorem C.5, with all matrix poles excluded by
the independently proved actual compact denominator estimate.
Article: jacobi, Corollary C.6.
Proof: apply the genuine complex spectral inverse theorem to the
unchanged original target basis. Zero padding contributes no extra
modes. Each true shifted coefficient is its actual normalized spectral
gap reciprocal, and the two genuine eigenvector square-root factors
cancel exactly with the original matrix dimension. -/
theorem finiteShiftedDiagonal_matrix (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) (w:ℂ)
    (hden:∀k:ℕ,1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2:ℝ):ℂ)*w≠0) :
    finiteShiftedDiagonal a b ha hb n i w=
      shiftedTargetResolvent a b ha hb n w i i/(((n:ℝ)+1:ℝ):ℂ) := by
  -- The inverse theorem is used only after genuine finite pole exclusion has been proved.
  have hg := jacobi.Finite.complex_resolvent_entry (targetMeasure a b ha hb n).reconstructed
    (targetMeasure a b ha hb n).reconstructedBasis (edgePoint n w)
    (shiftedTarget_gap_ne a b ha hb n w hden) i i
  unfold shiftedTargetResolvent
  change _=((edgePoint n w • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℂ)-
    (targetMeasure a b ha hb n).reconstructed.matrix.map Complex.ofRealHom)⁻¹) i i/_
  rw [hg,Finset.sum_div]
  unfold finiteShiftedDiagonal
  rw [tsum_eq_sum (s:=Finset.range (n+1)) (fun k hk => by
    simp only [finiteShiftedEdge,resolventTransform,jacobi.Jacobi.finiteLambdaAt_zero ha hb
      (by simpa only [Finset.mem_range,not_lt] using hk),Complex.ofReal_zero,zero_mul])]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [finiteShiftedEdge_gap a b ha hb n w hden k]
  simp only [scaledTargetEigenvector,targetEigenvectorEntry,dite_eq_left k.isLt,Complex.ofReal_mul,mul_pow]
  have hs : (sqrt ((n:ℝ)+1):ℂ)^2=(((n:ℝ)+1:ℝ):ℂ) := by
    exact_mod_cast sq_sqrt (by positivity : (0:ℝ)≤(n:ℝ)+1)
  rw [hs]
  have hgap := shiftedTarget_gap_ne a b ha hb n w hden k
  rw [show (targetMeasure a b ha hb n).reconstructedBasis.eigenvalues k=
    (jacobi.Jacobi.nodes a b ha hb (n+1)).value k from rfl]
  push_cast
  field_simp [hgap]

end
end jacobi.EdgeResolvent
