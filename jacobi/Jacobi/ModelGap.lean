import jacobi.Jacobi.ZeroModel
import jacobi.Oscillation.NodalCosineGap

/-!
Article: jacobi, Proposition B.1.
The article's literal affine cosine model has the same complete quadratic
finite pair-gap scale as the genuine Jacobi nodes. The affine scale is
proved at least one half at large degree; all model angles and endpoint
weights are the original printed formulas.
Use: preserves every explicit trigonometric model gap and makes the source interpolation coordinate legitimate.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology

/-- The actual affine cosine correction has a uniform positive scale beyond one fixed source-parameter degree threshold.
Use: preserves every explicit trigonometric model gap and makes the source interpolation coordinate legitimate.
Article: jacobi, Proposition B.1.
Proof: N tends to infinity; once N exceeds the absolute fixed endpoint
coefficient sum plus one, its square dominates that sum. The literal
inverse-square correction is then at most one quarter. -/
theorem modelScale_half (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop,(1/2:ℝ)≤modelScale a b n := by
  -- The source affine scale is bounded directly from its formula; no spectral model admissibility is assumed.
  let c := endpointCorrection a+endpointCorrection b
  filter_upwards [(frequency_tendsto a b).eventually (eventually_ge_atTop (|c|+1))] with n hn
  have hN : 0<frequency a b n := by linarith [abs_nonneg c]
  have hN2 : |c|≤frequency a b n^2 := by nlinarith [sq_nonneg (frequency a b n-1),abs_nonneg c]
  have hh : c/(4*frequency a b n^2)≤1/2 :=
    (div_le_iff₀ (by positivity : 0<4*frequency a b n^2)).mpr (by nlinarith [le_abs_self c,sq_nonneg (frequency a b n)])
  change 1/2≤1-c/(4*frequency a b n^2)
  linarith

/-- Every exact original model-angle difference is its literal pi/N index spacing.
Use: supplies the full angular separation for the corrected trigonometric model in Proposition B.1 (c).
Article: jacobi, Proposition B.1.
Proof: subtract the two explicit leading phase formulas and cast the actual ordered natural-index difference. -/
theorem modelAngle_difference (a b : ℝ) (n : ℕ) {i j : ℕ} (hij : i≤j) :
    modelAngle a b n j-modelAngle a b n i=Real.pi*((j-i:ℕ):ℝ)/frequency a b n := by
  unfold modelAngle phaseGrid
  rw [Nat.cast_sub hij]
  ring

/-- Every ordered pair of actual explicit corrected model nodes has the complete uniform quadratic source gap with a fixed positive constant.
Use: supplies the model-node separation assertion in Proposition B.1 (c), including both edges and all growing indices.
Article: jacobi, Proposition B.1.
Proof: the literal model angles have proved positive endpoint bounds
pi*(k+1)/(4*N) and exact pi/N spacing. The common two-sine finite geometry
lemma gives a cosine gap of one eighth of the source index weight. The
actual affine scale is at least one half and the shift cancels, giving
the stated one-sixteenth bound. Ordered pairs cover arbitrary pairs by symmetry. -/
theorem model_gap_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ i j : Fin n,i≤j →
        (1/16:ℝ)*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
          |modelNode a b n i.val-modelNode a b n j.val| := by
  -- Every model quantity is the literal printed expression; the only eventual input is the directly proved positive affine scale.
  filter_upwards [modelScale_half a b,eventually_ge_atTop (1:ℕ)] with n hn hnpos
  have hN := frequency_pos ha hb hnpos
  refine ⟨hN,?_⟩
  intro i j hij
  have hend : ∀ i : Fin n,(Real.pi/4)*(i.val+1:ℝ)/frequency a b n≤modelAngle a b n i.val ∧
      (Real.pi/4)*((n-i.val:ℕ):ℝ)/frequency a b n≤Real.pi-modelAngle a b n i.val :=
    fun i => (modelAngle_endpoint_bounds ha hb i.isLt).2
  have hspan : ∀ i j : Fin n,i≤j →
      (Real.pi/4)*((j.val-i.val:ℕ):ℝ)/frequency a b n≤modelAngle a b n j.val-modelAngle a b n i.val := by
    intro i j hij
    rw [modelAngle_difference a b n hij]
    apply div_le_div_of_nonneg_right _ hN.le
    have hz : (0:ℝ)≤((j.val-i.val:ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith [Real.pi_pos]
  have hc := nodal_cosine_gap (show 0<Real.pi/4 by positivity) hN
    (fun i => ⟨(modelAngle_endpoint_bounds ha hb i.isLt).1.1.le,(modelAngle_endpoint_bounds ha hb i.isLt).1.2.le⟩) hend hspan i j hij
  have hcoeff : 2*(Real.pi/4)^2/Real.pi^2=(1/8:ℝ) := by field_simp; norm_num
  rw [hcoeff] at hc
  have hmodel : |modelNode a b n i.val-modelNode a b n j.val|=
      modelScale a b n*|cos (modelAngle a b n i.val)-cos (modelAngle a b n j.val)| := by
    rw [modelNode,modelNode,show modelScale a b n*cos (modelAngle a b n i.val)+modelShift a b n-
      (modelScale a b n*cos (modelAngle a b n j.val)+modelShift a b n)=
      modelScale a b n*(cos (modelAngle a b n i.val)-cos (modelAngle a b n j.val)) by ring,
      abs_mul,abs_of_nonneg (by linarith : 0≤modelScale a b n)]
  rw [hmodel]
  have hh := mul_le_mul hn hc (by positivity) (by linarith : 0≤modelScale a b n)
  convert hh using 1
  dsimp [pairIndex]
  ring

end
end jacobi.Jacobi
