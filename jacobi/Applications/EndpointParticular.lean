import jacobi.Applications.NesterovModel

/-!
Article: jacobi, Theorem 5.1.
Explicit polynomial particular solutions reduce the actual covariance
recurrences to errors of orders zero, one and two. All identities are
rational identities on the original parameter range b>-1.
Use: EndpointCovarianceBounds compares these polynomials with the true
impulse covariances, and EndpointLimit extracts the original cubic limit.
-/
namespace jacobi.Applications
noncomputable section
set_option maxHeartbeats 2000000

/-- Slope of the difference variance particular solution.
Use: endpointDPoly is the linear particular solution in the genuine covariance estimate.
Article: jacobi, Theorem 5.1.
-/
def endpointA (b:ℝ) : ℝ := 1/(2*b+3)
/-- Constant term of the difference variance particular solution.
Use: endpointDPoly cancels the constant covariance forcing.
Article: jacobi, Theorem 5.1.
-/
def endpointB (b:ℝ) : ℝ := (3*b+1)/(2*(2*b+3))
/-- Positive rational forcing coefficient in the difference-variance error recurrence.
Use: the uniform error induction absorbs its decaying contribution by momentum contraction.
Article: jacobi, Theorem 5.1.
-/
def endpointK (b:ℝ) : ℝ := (b+1)^3/(2*(2*b+3))
/-- Quadratic coefficient in the cross covariance particular solution.
Use: determines the cubic leading coefficient of the actual endpoint gain.
Article: jacobi, Theorem 5.1.
-/
def endpointC (b:ℝ) : ℝ := endpointA b/(b+3)
/-- Linear coefficient in the cross covariance particular solution.
Use: endpointCPoly has an exact recurrence with forcing endpointDPoly.
Article: jacobi, Theorem 5.1.
-/
def endpointH (b:ℝ) : ℝ := (endpointA b+endpointB b-endpointC b*(b+1))/(b+2)
/-- Linear particular solution for the actual endpoint difference variance.
Use: its exact defect is bounded uniformly by the momentum contraction.
Article: jacobi, Theorem 5.1.
-/
def endpointDPoly (b x:ℝ) : ℝ := endpointA b*x+endpointB b
/-- Quadratic particular solution for the actual endpoint cross covariance.
Use: its error grows at most linearly when the difference-variance error stays bounded.
Article: jacobi, Theorem 5.1.
-/
def endpointCPoly (b x:ℝ) : ℝ := (x+b)*(endpointC b*x+endpointH b)
/-- Cubic particular solution for the actual original squared endpoint gain.
Use: its quadratic error vanishes after the original k^3 normalization.
Article: jacobi, Theorem 5.1.
-/
def endpointEPoly (b x:ℝ) : ℝ := 2*endpointC b/3*x^3+
  (endpointH b+endpointA b/2-2*endpointC b)*x^2+
  (-3*endpointH b+endpointA b/2+endpointB b+4*endpointC b/3)*x

/-- Every genuine positive-step momentum is a contraction on the original parameter range.
Use: controls all three actual covariance errors without logarithmic or Gamma-function cases.
Article: jacobi, Theorem 5.1.
Proof: k>=1 makes the numerator nonnegative, while b>-1 makes the denominator strictly larger than that numerator. -/
theorem nesterovMomentum_bounds {b:ℝ} (hb:-1<b) {k:ℕ} (hk:1≤k) :
    0≤nesterovMomentum b k ∧ nesterovMomentum b k≤1 := by
  have hkp:0<k:=by omega
  have hn:(1:ℝ)≤k:=by exact_mod_cast hk
  have hd:=nesterov_denominator_pos hb hkp
  simp only [nesterovMomentum,ite_eq_right (Nat.ne_of_gt hkp)]
  exact ⟨div_nonneg (by linarith) hd.le,(div_le_one hd).mpr (by linarith)⟩

/-- The exact linear difference-variance defect has a positive inverse-square forcing.
Use: EndpointCovarianceBounds bounds the true variance error by one constant.
Article: jacobi, Theorem 5.1.
Proof: all denominators are nonzero on b>-1 and k>=1; clearing them leaves a polynomial identity. -/
theorem endpointDPoly_recurrence {b:ℝ} (hb:-1<b) {k:ℕ} (hk:1≤k) :
    endpointDPoly b ((k:ℝ)+1)=(nesterovMomentum b k)^2*endpointDPoly b k+1-
      endpointK b/((k:ℝ)+b)^2 := by
  -- The defect is retained exactly rather than discarded in a formal asymptotic expansion.
  have hkp:0<k:=by omega
  have hd:((k:ℝ)+b)≠0:=(nesterov_denominator_pos hb hkp).ne'
  have ha:2*b+3≠0:=by linarith
  simp only [endpointDPoly,endpointA,endpointB,endpointK,nesterovMomentum,
    ite_eq_right (Nat.ne_of_gt hkp)]
  field_simp
  ring

/-- The quadratic cross particular solution satisfies the exact original covariance forcing.
Use: the true mixed error is bounded by the sum of the preceding bounded variance errors.
Article: jacobi, Theorem 5.1.
Proof: cancel the actual positive-step denominator and the nonzero original parameter factors, then verify the polynomial identity. -/
theorem endpointCPoly_recurrence {b:ℝ} (hb:-1<b) {k:ℕ} (hk:1≤k) :
    endpointCPoly b ((k:ℝ)+1)=nesterovMomentum b k*endpointCPoly b k+
      endpointDPoly b ((k:ℝ)+1) := by
  -- Positive original parameter factors justify clearing the exact covariance denominators.
  have hkp:0<k:=by omega
  have hd:((k:ℝ)+b)≠0:=(nesterov_denominator_pos hb hkp).ne'
  have ha:2*b+3≠0:=by linarith
  have hc:b+3≠0:=by linarith
  have hh:b+2≠0:=by linarith
  simp only [endpointCPoly,endpointDPoly,endpointH,endpointC,endpointA,endpointB,
    nesterovMomentum,ite_eq_right (Nat.ne_of_gt hkp)]
  field_simp
  ring

/-- The cubic gain particular solution satisfies the exact actual endpoint energy recurrence.
Use: its true covariance error grows only quadratically, so its cubic coefficient is the genuine limit.
Article: jacobi, Theorem 5.1.
Proof: the actual momentum denominator cancels the cross polynomial factor. The remaining finite polynomial identity is exact at every positive step. -/
theorem endpointEPoly_recurrence {b:ℝ} (hb:-1<b) {k:ℕ} (hk:1≤k) :
    endpointEPoly b ((k:ℝ)+1)=endpointEPoly b k+
      2*nesterovMomentum b k*endpointCPoly b k+endpointDPoly b ((k:ℝ)+1) := by
  -- Cancel the genuine momentum denominator against its cross-polynomial factor.
  have hkp:0<k:=by omega
  have hd:((k:ℝ)+b)≠0:=(nesterov_denominator_pos hb hkp).ne'
  have ha:2*b+3≠0:=by linarith
  have hc:b+3≠0:=by linarith
  have hh:b+2≠0:=by linarith
  simp only [endpointEPoly,endpointCPoly,endpointDPoly,endpointH,endpointC,endpointA,endpointB,
    nesterovMomentum,ite_eq_right (Nat.ne_of_gt hkp)]
  field_simp
  ring

end
end jacobi.Applications
