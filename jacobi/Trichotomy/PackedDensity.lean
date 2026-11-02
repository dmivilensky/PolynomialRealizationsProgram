import jacobi.Trichotomy.PackingInverse

/-!
Article: jacobi, Proposition 2.2.
The original profile is squared in its actual inverse intrinsic
coordinate and extended by zero off the true open coordinate image.
The density is nonnegative, positive exactly on that image and even.
No finite-support endpoint is postulated in this construction.
Use: packedDensity_mass, packedDensity_root_mass and packedDensity_energy give the source's exact mass, root mass and energy; endpoint coordinate limits identify its true support and tails.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan

/-- The actual packed persymmetric density, defined from the original profile and its genuine intrinsic coordinate inverse, with zero extension.
Use: packedDensity_mass, packedDensity_root_mass and packedDensity_energy give the source's exact mass, root mass and energy; endpoint coordinate limits identify its true support and tails.
Article: jacobi, Proposition 2.2.
-/
def packedDensity (a : ℝ) (ha : -1<a) (x : ℝ) : ℝ :=
  (packingImage a ha).indicator (fun y => (physicalProfile a ha (packingInverse a ha y))^2) x

/-- The genuine packed density vanishes outside its actual intrinsic coordinate image.
Use: whole-line density integrals are exactly their image integrals, and both compact and infinite support use the same source definition.
Article: jacobi, Proposition C.4.
Proof: this is the zero branch of the defining set indicator. -/
theorem packedDensity_zero_outside (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∉packingImage a ha) :
    packedDensity a ha x=0 := indicator_of_notMem hx _

/-- The genuine packed density has the original literal squared-profile formula on the actual coordinate interval.
Use: density positivity, evenness and every moment substitution retain precisely the article's normalization.
Article: jacobi, Proposition 2.2.
Proof: evaluate the defining indicator on its genuine positive domain. -/
theorem packedDensity_on_image (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    packedDensity a ha x=(physicalProfile a ha (packingInverse a ha x))^2 := indicator_of_mem hx _

/-- The original density evaluated in the original intrinsic coordinate is exactly the original profile squared.
Use: packed_composition_integral and its integrability equivalence make the full source moment substitutions literal.
Article: jacobi, Proposition 2.2.
Proof: use the actual coordinate's membership in its image and its independently proved inverse identity. -/
theorem packedDensity_coordinate (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    packedDensity a ha (packingCoordinate a ha t)=(physicalProfile a ha t)^2 := by
  rw [packedDensity_on_image a ha ⟨t,ht,rfl⟩,packingInverse_coordinate a ha ht]

/-- The actual packed source density is nonnegative everywhere.
Use: its root mass and positive real-power energy have their ordinary nonnegative meanings on the whole real line.
Article: jacobi, Proposition 2.2.
Proof: the defining nonzero branch is a real square and the extension is zero. -/
theorem packedDensity_nonneg (a : ℝ) (ha : -1<a) (x : ℝ) : 0≤packedDensity a ha x :=
  indicator_nonneg (fun _ _ => sq_nonneg _) x

/-- The genuine packed density is positive exactly on the true intrinsic coordinate image.
Use: the topological support is its closure, and the endpoint regime determines whether that closure is the real line or a compact centered interval.
Article: jacobi, Proposition C.4.
Proof: on the coordinate image the inverse is physical interior and the true profile is strictly positive. Outside the image the density is zero. -/
theorem packedDensity_pos_iff (a : ℝ) (ha : -1<a) (x : ℝ) :
    0<packedDensity a ha x ↔ x∈packingImage a ha := by
  constructor
  · intro h
    by_contra hx
    rw [packedDensity_zero_outside a ha hx] at h
    exact lt_irrefl 0 h
  · intro hx
    rw [packedDensity_on_image a ha hx]
    exact sq_pos_of_pos (physicalProfile_pos a ha (packingInverse_mem a ha hx))

/-- The actual intrinsic coordinate image is invariant under sign reversal.
Use: the true inverse and packed density inherit the source's centered reflection symmetry in both support regimes.
Article: jacobi, Proposition C.4.
Proof: reflect each actual physical preimage by t to 1-t and use the independently proved exact coordinate reflection. -/
theorem packingImage_neg (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    -x∈packingImage a ha := by
  obtain ⟨t,ht,rfl⟩ := hx
  exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,packingCoordinate_reflection a ha t⟩

/-- The actual inverse coordinate reflects physical points about the original midpoint.
Use: packedDensity_even derives evenness of the actual constructed density rather than assuming it.
Article: jacobi, Proposition C.4.
Proof: the physical reflected inverse has coordinate -x. Injectivity of the genuine coordinate identifies it with the inverse at -x. -/
theorem packingInverse_reflection (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    packingInverse a ha (-x)=1-packingInverse a ha x := by
  have hm := packingInverse_mem a ha hx
  apply (packingCoordinate_strictMono a ha).injOn (packingInverse_mem a ha (packingImage_neg a ha hx))
    ⟨by linarith [hm.2],by linarith [hm.1]⟩
  rw [packingCoordinate_inverse a ha (packingImage_neg a ha hx),packingCoordinate_reflection,
    packingCoordinate_inverse a ha hx]

/-- The actual original packed persymmetric density is even on the whole real line, including its zero extension.
Use: both spatial ends have the same genuine tail asymptotic and the source moment identities concern the centered density.
Article: jacobi, Proposition 2.2.
Proof: inside the true image, inverse-coordinate reflection and original profile reflection preserve the square. Outside, the centered image symmetry makes both density values zero. -/
theorem packedDensity_even (a : ℝ) (ha : -1<a) (x : ℝ) :
    packedDensity a ha (-x)=packedDensity a ha x := by
  by_cases hx : x∈packingImage a ha
  · rw [packedDensity_on_image a ha (packingImage_neg a ha hx),packedDensity_on_image a ha hx,
      packingInverse_reflection a ha hx,physicalProfile_reflection]
  · have hn : -x∉packingImage a ha := fun h => hx (by simpa only [neg_neg] using packingImage_neg a ha h)
    rw [packedDensity_zero_outside a ha hx,packedDensity_zero_outside a ha hn]

end
end jacobi.Trichotomy
