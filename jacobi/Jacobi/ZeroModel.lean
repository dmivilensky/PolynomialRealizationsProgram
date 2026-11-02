import jacobi.Jacobi.EndpointGeometry

/-!
Article: jacobi, Proposition B.1.
These are precisely the article's corrected trigonometric zero model and
its index weights, with indices shifted down by one. All subsequent
error and gap statements compare these literal objects with the actual
original sorted finite Jacobi nodes.
Use: the exact reference angles in Proposition B.1 (a)--(d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology

/-- The source's leading angular grid at the actual finite Jacobi frequency.
Use: the exact reference angles in Proposition B.1 (a)--(d).
Article: jacobi, Proposition B.1.
-/
def modelAngle (a b : ℝ) (n k : ℕ) : ℝ := phaseGrid a k/frequency a b n

/-- The literal source affine cosine scale.
Use: the original corrected trigonometric model in Proposition B.1 (b)--(d).
Article: jacobi, Proposition B.1.
-/
def modelScale (a b : ℝ) (n : ℕ) : ℝ :=
  1-(endpointCorrection a+endpointCorrection b)/(4*frequency a b n^2)

/-- The literal source affine cosine shift.
Use: the original two-edge correction in the finite zero model.
Article: jacobi, Proposition B.1.
-/
def modelShift (a b : ℝ) (n : ℕ) : ℝ :=
  (endpointCorrection b-endpointCorrection a)/(4*frequency a b n^2)

/-- The actual explicit corrected trigonometric zero model from the article.
Use: model-node separation and the original error and interpolation assertions in Proposition B.1 (b)--(d).
Article: jacobi, Proposition B.1.
-/
def modelNode (a b : ℝ) (n k : ℕ) : ℝ :=
  modelScale a b n*cos (modelAngle a b n k)+modelShift a b n

/-- The source's distance of an original zero index from its nearer finite endpoint.
Use: the exact uniform two-edge error, distance and interpolation weights.
Article: jacobi, Proposition B.1.
-/
def edgeIndex (n k : ℕ) : ℕ := min (k+1) (n-k)

/-- The source's sum-of-indices distance of a pair from its nearer finite endpoint.
Use: the exact quadratic original-node and model-node gap scale in Proposition B.1 (c).
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def pairIndex (n k l : ℕ) : ℕ := min (k+l+2) (2*n-k-l)

/-- The original model angles reflect exactly after exchanging the two source parameters and reversing their actual finite indices.
Use: supplies both model endpoint scales and the opposite-edge statements of Proposition B.1.
Article: jacobi, Proposition B.1.
Proof: the two exact phase grids sum to pi*N at reverse indices; divide by the actual positive frequency. -/
theorem modelAngle_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    modelAngle a b n (n-1-k)=Real.pi-modelAngle b a n k := by
  -- Exact affine phase arithmetic fixes the model reflection before any zero-error bound is used.
  have hN := frequency_pos ha hb (show 0<n by omega)
  have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
  have hp : phaseGrid a (n-1-k)+phaseGrid b k=Real.pi*frequency a b n := by
    unfold phaseGrid frequency
    rw [show (n-1-k:ℕ)=n-(k+1) by omega,Nat.cast_sub (show k+1≤n by omega)]
    push_cast
    ring
  unfold modelAngle
  rw [hfreq]
  apply eq_sub_iff_add_eq.mpr
  rw [← add_div,hp]
  exact mul_div_cancel_right₀ _ hN.ne'


/-- Every original model angle is positive, below pi, and has the same universal linear lower bound at both endpoints.
Use: gives the complete model-node gap scale in Proposition B.1 (c), without a model endpoint premise.
Article: jacobi, Proposition B.1.
Proof: the original leading phase lower bound applies at each endpoint;
exact parameter/index reflection identifies the opposite endpoint. -/
theorem modelAngle_endpoint_bounds {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    modelAngle a b n k∈Ioo 0 Real.pi ∧
      (Real.pi/4)*(k+1:ℝ)/frequency a b n≤modelAngle a b n k ∧
      (Real.pi/4)*((n-k:ℕ):ℝ)/frequency a b n≤Real.pi-modelAngle a b n k := by
  -- The exact reflected phase handles arbitrary unequal source parameters and every actual finite model index.
  have hN := frequency_pos ha hb (show 0<n by omega)
  have hlo := div_le_div_of_nonneg_right (phaseGrid_lower ha k) hN.le
  have hrev := div_le_div_of_nonneg_right (phaseGrid_lower hb (n-1-k)) hN.le
  have he := modelAngle_reflection hb ha hk
  have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
  rw [← hfreq] at hrev
  change (Real.pi/4)*(((n-1-k:ℕ):ℝ)+1)/frequency b a n≤modelAngle b a n (n-1-k) at hrev
  have hcast : ((n-1-k:ℕ):ℝ)+1=((n-k:ℕ):ℝ) := by
    have hh : n-1-k+1=n-k := by omega
    exact_mod_cast hh
  rw [he,hcast,hfreq] at hrev
  refine ⟨⟨div_pos (phaseGrid_pos ha k) hN,?_⟩,hlo,hrev⟩
  have hp : 0<(Real.pi/4)*((n-k:ℕ):ℝ)/frequency a b n := by
    have hh : 0<n-k := by omega
    have hhR : (0:ℝ)<((n-k:ℕ):ℝ) := by exact_mod_cast hh
    positivity
  linarith

end
end jacobi.Jacobi
