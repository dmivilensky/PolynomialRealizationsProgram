import jacobi.Jacobi.EndpointMargins
import jacobi.Oscillation.InterpolationGeometry

/-!
Article: jacobi, Proposition B.1.
The exact inverse affine coordinate sends the two original interpolation
endpoints to their proved positive squared distances. Affineness keeps
every intermediate point inside the same quantitative bounds. The
opposite endpoint factor is bounded independently using the true angular
cap and the literal scale and shift tending to one and zero.
Use: interpolates the positive true and model margins in Proposition B.1 (d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual squared right-endpoint distance in the inverse of the source's affine cosine coordinate.
Use: interpolates the positive true and model margins in Proposition B.1 (d).
Article: jacobi, Proposition B.1.
-/
def interpolationDistance (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (frequency a b n)^2*(1-(x-modelShift a b n)/modelScale a b n)

/-- The affine coordinate has exactly the true corrected distance at the genuine finite node and the literal model distance at the model node.
Use: transfers the unconditional endpoint margins to the whole interpolation interval.
Article: jacobi, Proposition B.1.
Proof: substitute the literal source scale and shift, clear their nonzero denominators, and use their exact endpoint correction identity. -/
theorem interpolationDistance_endpoints {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ}
    (hN : 0<frequency a b n) (hscale : modelScale a b n≠0) (k : ℕ) :
    interpolationDistance a b n (cos (finiteAngleAt a b ha hb n k))=
      correctedSquaredDistance a b ha hb n k ∧
    interpolationDistance a b n (modelNode a b n k)=modelSquaredDistance a b n k := by
  -- The positive margin uses the actual affine endpoint shift, not the unshifted Jacobi distance.
  have he : (frequency a b n)^2*(modelScale a b n+modelShift a b n-1)= -endpointCorrection a/2 := by
    dsimp [modelScale,modelShift]
    field_simp [hN.ne']
    ring
  constructor
  · unfold interpolationDistance correctedSquaredDistance
    field_simp [hscale]
    nlinarith [he]
  · unfold interpolationDistance modelNode modelSquaredDistance
    field_simp [hscale]
    ring

/-- Every point between the actual model and genuine first-half node retains both positive quadratic endpoint-distance bounds.
Use: supplies the first endpoint factor for the sine comparison throughout the interpolation interval.
Article: jacobi, Proposition B.1.
Proof: evaluate the exact inverse affine distance at both endpoints and apply the elementary affine interval lemma. -/
theorem interpolationDistance_bounds {a b d D : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ}
    (hN : 0<frequency a b n) (hscale : modelScale a b n≠0)
    (hactual : correctedSquaredDistance a b ha hb n k ∈ Icc (d*(k+1:ℝ)^2) (D*(k+1:ℝ)^2))
    (hmodel : modelSquaredDistance a b n k ∈ Icc (d*(k+1:ℝ)^2) (D*(k+1:ℝ)^2))
    {x : ℝ} (hx : x ∈ uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k))) :
    interpolationDistance a b n x ∈ Icc (d*(k+1:ℝ)^2) (D*(k+1:ℝ)^2) := by
  -- Affine preservation applies without knowing which endpoint is larger.
  obtain ⟨hactualEq,hmodelEq⟩ := interpolationDistance_endpoints ha hb hN hscale k
  rw [← hactualEq] at hactual
  rw [← hmodelEq] at hmodel
  let A := -(frequency a b n)^2/modelScale a b n
  let B := (frequency a b n)^2*(1+modelShift a b n/modelScale a b n)
  have heq : ∀ z,interpolationDistance a b n z=A*z+B := by
    intro z
    dsimp [interpolationDistance,A,B]
    ring
  rw [heq] at hactual hmodel ⊢
  exact affine_interval_bounds hmodel hactual hx

/-- Every original first-half interpolation segment has a fixed lower bound on its inverse affine cosine coordinate.
Use: bounds 1+cos(theta) away from zero independently of the positive right-endpoint margin in Proposition B.1 (d).
Article: jacobi, Proposition B.1.
Proof: genuine and model first-half angles are at most 3*pi/4. Their
cosines are at least -3/4. The actual scale is eventually at least 7/8
and the actual shift at most 1/16 in absolute value. Both inverse affine
endpoint coordinates are then at least -15/16; affine interpolation
preserves that bound. -/
theorem firstHalf_interpolation_opposite {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∀ᶠ n : ℕ in atTop,0<modelScale a b n ∧ ∀ k,2*k<n → ∀ x : ℝ,
      x ∈ uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k)) →
        -(15/16:ℝ)≤(x-modelShift a b n)/modelScale a b n := by
  -- The opposite factor is controlled separately: positive right-endpoint distance alone would not exclude the other angular endpoint.
  have hscale := (modelScale_tendsto a b).eventually (Ioi_mem_nhds (by norm_num : (7/8:ℝ)<1))
  have hshift := ((modelShift_tendsto a b).abs).eventually (Iio_mem_nhds (by norm_num : |(0:ℝ)|<1/16))
  filter_upwards [hscale,hshift,firstHalf_angle_cap ha hb,firstHalf_modelAngle_cap a b] with n hsc hsh hcap hmodel
  have hs : 0<modelScale a b n := by linarith
  refine ⟨hs,?_⟩
  intro k hk x hx
  have hkn : k<n := by omega
  have hactualAngle := (angle_properties ha hb (⟨k,hkn⟩ : Fin n)).1
  have ha0 : 0≤finiteAngleAt a b ha hb n k := by
    rw [finiteAngleAt_eq ha hb hkn]
    exact hactualAngle.1.le
  have hac := cosine_cap_lower ⟨ha0,hcap k hk⟩
  have hmc := cosine_cap_lower ⟨(modelAngle_endpoint_bounds ha hb hkn).1.1.le,hmodel.2 k hk⟩
  have hactual : -(15/16:ℝ)≤(cos (finiteAngleAt a b ha hb n k)-modelShift a b n)/modelScale a b n := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [(abs_lt.mp hsh).2]
  have hmodelEq : (modelNode a b n k-modelShift a b n)/modelScale a b n=cos (modelAngle a b n k) := by
    unfold modelNode
    field_simp [hs.ne']
    ring
  have hmodelLower : -(15/16:ℝ)≤(modelNode a b n k-modelShift a b n)/modelScale a b n := by
    rw [hmodelEq]
    linarith
  let A := 1/modelScale a b n
  let B := -modelShift a b n/modelScale a b n
  have heq : ∀ z,(z-modelShift a b n)/modelScale a b n=A*z+B := by intro z; dsimp [A,B]; ring
  have hupper : (modelNode a b n k-modelShift a b n)/modelScale a b n≤
      max ((modelNode a b n k-modelShift a b n)/modelScale a b n)
        ((cos (finiteAngleAt a b ha hb n k)-modelShift a b n)/modelScale a b n) := le_max_left _ _
  have hupper' : (cos (finiteAngleAt a b ha hb n k)-modelShift a b n)/modelScale a b n≤
      max ((modelNode a b n k-modelShift a b n)/modelScale a b n)
        ((cos (finiteAngleAt a b ha hb n k)-modelShift a b n)/modelScale a b n) := le_max_right _ _
  simp only [heq] at hmodelLower hactual hupper hupper' ⊢
  exact (affine_interval_bounds ⟨hmodelLower,hupper⟩ ⟨hactual,hupper'⟩ hx).1

end
end jacobi.Jacobi
