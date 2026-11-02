import jacobi.Variational.FredholmGradient
import jacobi.Continuum.FunctionalTrace

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
The regularized logarithm is realized as a genuine positive trace-class
spectral function of the actual density operator, with its exact trace in
every Hilbert basis. All eigenbasis values lie in the proved subcritical
domain. The scalar supporting-line inequality follows directly from
log(r)<=r-1 and prepares the operator trace comparison.
Source: complete compact spectral data and the elementary logarithm inequality.
Use: sorting invariance needs a globally nonnegative scalar function; on the actual subcritical spectrum this is exactly f_s.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- A nonnegative real extension used only to construct subcritical spectral functional calculus.
Use: sorting invariance needs a globally nonnegative scalar function; on the actual subcritical spectrum this is exactly f_s.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def fredholmCutoff (s x : ℝ) : ℝ := if s*x<1 then fredholmLog s x else 0

/-- The cutoff vanishes at the zero eigenvalue.
Use: spectral sorting and zero padding preserve the actual Fredholm trace.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: zero lies below the pole and its regularized logarithm is zero. -/
theorem fredholmCutoff_zero (s : ℝ) : fredholmCutoff s 0=0 := by simp [fredholmCutoff]

/-- The auxiliary real extension is nonnegative everywhere.
Use: the positive spectral function theorem applies without an unproved sign condition outside the actual spectrum.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: below the pole use the proved logarithm bound, and on the unused branch the value is zero. -/
theorem fredholmCutoff_nonneg (s x : ℝ) : 0≤fredholmCutoff s x := by
  unfold fredholmCutoff
  split_ifs with h
  · exact fredholmLog_nonneg h
  · exact le_rfl

/-- The printed top spectral margin bounds every actual feature eigenbasis eigenvalue.
Use: identifies the spectral function with the true logarithm on the full complete eigenbasis.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: each eigenbasis eigenvalue is bounded by the same actual sorted top value. -/
theorem L1Source.eigenbasis_margin (m : L1Source) {s ε : ℝ} (hs : 0≤s)
    (hp : s*observe m .top≤1-ε) (i : (densitySpectralData m.integrable m.nonneg).Index) :
    s*(densitySpectralData m.integrable m.nonneg).eig i≤1-ε := by
  let D := densitySpectralData m.integrable m.nonneg
  have he := density_kernel_eigenvalue_eq m.integrable m.nonneg D
  have h := jacobi.Continuum.eigenbasis_le_top D i
  rw [he] at h
  change D.eig i≤observe m .top at h
  exact (mul_le_mul_of_nonneg_left h hs).trans hp

/-- The actual eigenbasis logarithmic values are absolutely summable under the printed pole condition.
Use: constructs f_s(K_m) in nuclear functional calculus with no small-mass assumption.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: use the proved scalar Lipschitz summability bound on the complete actual eigenbasis. -/
theorem L1Source.fredholm_eigenbasis_summable (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    Summable (fun i => fredholmCutoff s ((densitySpectralData m.integrable m.nonneg).eig i)) := by
  -- Every basis eigenvalue uses the subcritical branch; the extension never changes an actual value.
  let ε := 1-s*observe m .top
  have hε : 0<ε := sub_pos.mpr hp
  have hmargin : s*observe m .top≤1-ε := by dsimp only [ε]; linarith
  have h := fredholmLog_summable hs hε (densitySpectralData m.integrable m.nonneg).summable
    (densitySpectralData m.integrable m.nonneg).nonneg (m.eigenbasis_margin hs hmargin)
  apply h.congr
  intro i
  have hip : s*(densitySpectralData m.integrable m.nonneg).eig i<1 := by
    have hh := m.eigenbasis_margin hs hmargin i
    linarith
  simp only [fredholmCutoff,ite_eq_left hip]

/-- The actual regularized logarithmic spectral function operator.
Use: Klein's comparison uses its actual trace in a different operator's eigenbasis.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def L1Source.fredholmFunction (m : L1Source) (s : ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  diagonalOperator (densitySpectralData m.integrable m.nonneg).basis
    (fun i => fredholmCutoff s ((densitySpectralData m.integrable m.nonneg).eig i))

/-- The actual spectral function acts by the genuine subcritical logarithm on every eigenbasis vector.
Use: evaluates both diagonal and off-basis quadratic forms in Klein's proof.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: the nuclear diagonal operator has its established eigenvector action;
the actual top margin places every eigenvalue on the true logarithmic branch. -/
theorem L1Source.fredholmFunction_basis (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (i : (densitySpectralData m.integrable m.nonneg).Index) :
    m.fredholmFunction s ((densitySpectralData m.integrable m.nonneg).basis i)=
      fredholmLog s ((densitySpectralData m.integrable m.nonneg).eig i) •
        (densitySpectralData m.integrable m.nonneg).basis i := by
  -- Actual subcriticality is checked for the entire basis, including the zero eigenspace.
  have hmarg : s*observe m .top≤1-(1-s*observe m .top) := by linarith
  unfold L1Source.fredholmFunction
  rw [diagonalOperator_basis _ (m.fredholm_eigenbasis_summable hs hp).abs]
  have hip : s*(densitySpectralData m.integrable m.nonneg).eig i<1 := by
    have h := m.eigenbasis_margin hs hmarg i
    linarith
  rw [fredholmCutoff,ite_eq_left hip]

/-- The actual logarithmic spectral function has its true Fredholm trace in every Hilbert basis.
Use: permits summing Klein's pointwise comparison in the eigenbasis of the other actual operator.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: use the basis-independent positive spectral function trace and
sorting invariance, then identify every actual sorted eigenvalue's logarithmic branch. -/
theorem L1Source.fredholmFunction_trace (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace) :
    HasSum (fun i => inner ℝ (b i) (m.fredholmFunction s (b i))) (m.fredholmReal s) := by
  -- This is a trace identity for a genuine operator, rather than a definition by scalar summation.
  let D := densitySpectralData m.integrable m.nonneg
  have h := jacobi.Continuum.positiveFunction_hasSum_trace D (fredholmCutoff s)
    (fredholmCutoff_zero s) (fun x _ => fredholmCutoff_nonneg s x)
    (m.fredholm_eigenbasis_summable hs hp) b
  have he : D.eigenvalue=m.spectrum := density_kernel_eigenvalue_eq m.integrable m.nonneg D
  rw [he] at h
  have hmarg : s*observe m .top≤1-(1-s*observe m .top) := by linarith
  have hsum : (∑' n,fredholmCutoff s (m.spectrum n))=m.fredholmReal s := by
    apply tsum_congr
    intro n
    have hnp : s*m.spectrum n<1 := by have h := m.spectral_margin hs hmarg n; linarith
    rw [fredholmCutoff,ite_eq_left hnp]
  rw [hsum] at h
  exact h

/-- The exact scalar supporting-line inequality for the subcritical regularized logarithm.
Use: the eigenbasis proof of the Fredholm Klein inequality and its quadratic variation remainder.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: put r=(1-s*z)/(1-s*x)>0. The supporting-line error is exactly
r-1-log(r), which is nonnegative by the proved logarithm inequality. -/
theorem fredholmLog_supporting {s x z : ℝ} (hx : s*x<1) (hz : s*z<1) :
    fredholmLog s x+(s/(1-s*x)-s)*(z-x)≤fredholmLog s z := by
  -- The ratio proof controls the actual full subcritical interval directly.
  have hA : 0<1-s*x := sub_pos.mpr hx
  have hB : 0<1-s*z := sub_pos.mpr hz
  have h := log_le_sub_one_of_pos (div_pos hB hA)
  have he : fredholmLog s z-fredholmLog s x-(s/(1-s*x)-s)*(z-x)=
      (1-s*z)/(1-s*x)-1-log ((1-s*z)/(1-s*x)) := by
    rw [fredholmLog,fredholmLog,log_div hB.ne' hA.ne']
    field_simp
    ring
  have hnon : 0≤fredholmLog s z-fredholmLog s x-(s/(1-s*x)-s)*(z-x) := by rw [he]; linarith
  linarith

end
end jacobi.Variational
