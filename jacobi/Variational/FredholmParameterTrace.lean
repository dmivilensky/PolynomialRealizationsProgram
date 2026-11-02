import jacobi.Variational.FredholmParameter
import jacobi.Variational.FredholmKlein

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The summable logarithmic parameter derivative equals the actual nuclear
trace of (R-I)*K_m. Its feature trace is exactly integral m*(2g-1), so the
real spectral determinant has the actual Green-diagonal parameter derivative.
Sorting includes every nonzero eigenvalue and its multiplicity; its zero
padding contributes zero. No unproved trace differentiation rule is used.
Source: the proved spectral series derivative and nuclear rank-one trace integral.
Use: spectral sorting preserves the nuclear parameter trace without assigning a finite determinant at a pole.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- A nonnegative scalar extension used to sort the actual subcritical determinant derivative spectrum.
Use: spectral sorting preserves the nuclear parameter trace without assigning a finite determinant at a pole.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def fredholmSlopeCutoff (s x : ℝ) : ℝ := if s*x<1 then s*x^2/(1-s*x) else 0

/-- The parameter-derivative extension vanishes on the zero eigenspace.
Use: permits the actual sorted spectrum to include its zero padding.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: substitute zero into the exact scalar formula. -/
theorem fredholmSlopeCutoff_zero (s : ℝ) : fredholmSlopeCutoff s 0=0 := by simp [fredholmSlopeCutoff]

/-- The parameter-derivative extension is nonnegative for every nonnegative coupling.
Use: licenses the proved sorting invariance of the actual nonnegative spectral trace.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: below the pole all numerator factors are nonnegative and the denominator is positive; elsewhere the unused extension is zero. -/
theorem fredholmSlopeCutoff_nonneg {s : ℝ} (hs : 0≤s) (x : ℝ) : 0≤fredholmSlopeCutoff s x := by
  unfold fredholmSlopeCutoff
  split_ifs with h
  · exact div_nonneg (mul_nonneg hs (sq_nonneg x)) (sub_pos.mpr h).le
  · exact le_rfl

/-- The actual spectral parameter slope equals the literal Green-diagonal nuclear trace integral.
Use: matches the determinant parameter derivative with the spatial Green identity's derivative.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: form the actual nuclear product (R-I)*K_m. Its actual complete
operator eigenbasis diagonal is the displayed scalar slope. Nuclear trace
summability and proved spectral sorting identify its sum with the genuine
spectral sequence; the feature trace integral gives the same physical Green expression. -/
theorem L1Source.fredholm_parameter_trace (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    (∑' n,s*m.spectrum n^2/(1-s*m.spectrum n))=
      ∫ x,m.value x*(2*m.fredholmGreen s hs hp x x-1) := by
  -- The derivative trace is an actual nuclear operator product before any diagonal is evaluated.
  let D := densitySpectralData m.integrable m.nonneg
  let A := m.fredholmResolvent s hs hp-ContinuousLinearMap.id ℝ FeatureSpace
  let U := jacobi.Continuum.composedDensity A m.value
  have hmargin : s*observe m .top≤1-(1-s*observe m .top) := by linarith
  have hip (i : D.Index) : s*D.eig i<1 := by have hh := m.eigenbasis_margin hs hmargin i; linarith
  have hdiag (i : D.Index) : inner ℝ (D.basis i) (U.val (D.basis i))=fredholmSlopeCutoff s (D.eig i) := by
    change inner ℝ (D.basis i) ((jacobi.Continuum.composedDensity A m.value).val (D.basis i))=_
    rw [jacobi.Continuum.composedDensity_val A m.integrable]
    change inner ℝ (D.basis i) (A (densityOperator m.value (D.basis i)))=_
    rw [D.equation,map_smul,real_inner_smul_right]
    change D.eig i*inner ℝ (D.basis i)
      (m.fredholmResolvent s hs hp (D.basis i)-D.basis i)=_
    rw [inner_sub_right,m.fredholmResolvent_basis hs hp,
      real_inner_smul_right,real_inner_self_eq_norm_sq,D.basis.orthonormal.norm_eq_one,one_pow]
    change D.eig i*((1-s*D.eig i)⁻¹*1-1)=fredholmSlopeCutoff s (D.eig i)
    unfold fredholmSlopeCutoff
    rw [ite_eq_left (hip i)]
    apply (eq_div_iff (sub_pos.mpr (hip i)).ne').mpr
    calc
      _ = D.eig i*((1-s*D.eig i)⁻¹*(1-s*D.eig i)-(1-s*D.eig i)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (sub_pos.mpr (hip i)).ne']; ring
  have hsum : HasSum (fun i => fredholmSlopeCutoff s (D.eig i)) (TraceClassOperator.trace D.basis U) := by
    have hh : HasSum (fun i => inner ℝ (D.basis i) (U.val (D.basis i)))
        (TraceClassOperator.trace D.basis U) := (traceClass_diagonal_summable D.basis U).1.of_abs.hasSum
    convert hh using 1
    funext i
    exact (hdiag i).symm
  have hsort := (spectralSorted_moment D.summable D.nonneg (fredholmSlopeCutoff s)
    (fredholmSlopeCutoff_zero s) (fun x _ => fredholmSlopeCutoff_nonneg hs x) hsum.summable).2
  change (∑' n,fredholmSlopeCutoff s (D.eigenvalue n))=∑' i,fredholmSlopeCutoff s (D.eig i) at hsort
  rw [density_kernel_eigenvalue_eq m.integrable m.nonneg D] at hsort
  have htrace : TraceClassOperator.trace D.basis U=
      ∫ x,m.value x*(2*m.fredholmGreen s hs hp x x-1) := by
    rw [jacobi.Continuum.composedDensity_trace D.basis A m.integrable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change m.value x*inner ℝ
        (m.fredholmResolvent s hs hp (feature x)-feature x) (feature x)=_
      rw [inner_sub_left,real_inner_self_eq_norm_sq,feature_norm]
      unfold L1Source.fredholmGreen
      ring
  calc
    _ = ∑' n,fredholmSlopeCutoff s (m.spectrum n) := tsum_congr fun n => by
      unfold fredholmSlopeCutoff
      rw [ite_eq_left (by have hh := m.spectral_margin hs hmargin n; linarith)]
    _ = ∑' i,fredholmSlopeCutoff s (D.eig i) := hsort
    _ = TraceClassOperator.trace D.basis U := hsum.tsum_eq
    _ = _ := htrace

/-- The actual real determinant parameter derivative is its genuine physical Green-diagonal trace.
Use: completes the spectral derivative side of the spatial determinant integral formula.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: combine the proved actual spectral series derivative with the proved actual nuclear trace equality. -/
theorem L1Source.fredholmReal_green_hasDerivAt (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    HasDerivAt m.fredholmReal (∫ x,m.value x*(2*m.fredholmGreen s hs hp x x-1)) s := by
  rw [← m.fredholm_parameter_trace hs hp]
  exact m.fredholmReal_hasDerivAt hs hp

end
end jacobi.Variational
