import jacobi.GelfandLevitan.SpatialIncrement

/-!
Article: jacobi, Theorem 2.1.
The original diagonal has its genuine continuous derivative, equal to
the sum of the two proved actual partial derivatives. Its true quotient
splits into a fixed-spatial-coordinate quotient and an independently
identified shrinking average of the actual spatial derivative.
Use: kernelDiagonal_hasDerivWithinAt identifies this precise original expression with w', completing Differentiability of K (c) and fixing the derivative in the transformed potential.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel

/-- The sum of the actual original partial derivatives evaluated on the original positive diagonal, continuously in its physical parameter.
Use: kernelDiagonal_hasDerivWithinAt identifies this precise original expression with w', completing Differentiability of K (c) and fixing the derivative in the transformed potential.
Article: jacobi, Theorem 2.1.
-/
def diagonalSlopeRows {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ)) : C(DerivativeStrip d,ℝ) :=
  ⟨fun t => derivativeCandidateRows ha hd t (halfInclusion (derivativeStripInclusion hd t))+
    secondDerivativeMap ha hd hds (t,t),
    ((transformationKernel_firstDerivative_continuous ha hd).comp
      (continuous_id.prodMk (derivativeStripInclusion hd).continuous)).add
      ((secondDerivativeMap ha hd hds).continuous.comp (continuous_id.prodMk continuous_id))⟩

/-- The original diagonal has the sum of its genuine actual partial derivatives as its true right derivative at every positive physical point below the midpoint.
Use: kernelDiagonal_hasDerivWithinAt extends this actual derivative continuously to the complete closed positive interval, including the midpoint.
Article: jacobi, Theorem 2.1.
Proof: split the literal diagonal difference quotient at K(u,t). The fixed-spatial-coordinate quotient has the already proved actual t derivative. The other quotient is exactly the true spatial derivative's shrinking affine average and converges to its actual diagonal value by continuity. Add these genuine limits. -/
theorem kernelDiagonal_hasDerivWithinAt_right {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) (htop : (t:ℝ)<1/2) :
    HasDerivWithinAt (fun x : ℝ => kernelDiagonal a ha (halfParameterClamp x))
      (diagonalSlopeRows ha hd (hdt.trans t.property.2) ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩) (Ici (t:ℝ)) (t:ℝ) := by
  -- Both summands are genuine original difference quotients; the diagonal derivative is a consequence of their independently proved limits.
  have hds := hdt.trans t.property.2
  have ht := transformationKernel_hasDerivWithinAt_right ha hd t t hdt htop le_rfl
  have hlimt := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mp ht.Ioi_of_Ici
  have hself : halfParameterClamp (t:ℝ)=t := Set.projIcc_of_mem (by norm_num) t.property
  have hlimc : Tendsto (fun x : ℝ => halfParameterClamp x) (𝓝[>] (t:ℝ)) (𝓝 t) := by
    simpa only [hself] using (halfParameterClamp.continuous.continuousAt (x := (t:ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (t:ℝ)))
  have hlims := (affineAverage_tendsto (positiveSecondDerivative ha hd hds) t).comp hlimc
  rw [positiveSecondDerivative_apply ha hd hds t t hdt hdt] at hlims
  have hlim := hlimt.add hlims
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mpr
  change Tendsto _ _ (𝓝 (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (halfInclusion t)+
    secondDerivativeValue ha hd hds t ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT htop] with x hx
  have hp : x∈Icc (0:ℝ) (1/2) := ⟨t.property.1.trans hx.1.le,hx.2.le⟩
  have he : halfParameterClamp x=(⟨x,hp⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) hp
  have hn : (⟨x,hp⟩:HalfInterval)≠t := fun h => hx.1.ne' (congrArg Subtype.val h)
  dsimp only [Function.comp_apply]
  rw [slope_def_module,slope_def_module,smul_eq_mul,smul_eq_mul,hself,he,
    spatialIncrement_average ha hd hds t ⟨x,hp⟩ hdt hx.1.le hn]
  change (x-(t:ℝ))⁻¹*(transformationKernel a ha ⟨x,hp⟩ t-transformationKernel a ha t t)+
    (x-(t:ℝ))⁻¹*(transformationKernel a ha ⟨x,hp⟩ ⟨x,hp⟩-transformationKernel a ha ⟨x,hp⟩ t)=
    (x-(t:ℝ))⁻¹*(transformationKernel a ha ⟨x,hp⟩ ⟨x,hp⟩-transformationKernel a ha t t)
  ring

/-- The actual original diagonal has its genuine continuous derivative throughout every required positive physical interval, including its midpoint left derivative.
Use: completes Differentiability of K (c), and supplies the actual derivative w' used in the original transformed differential equation and the target potential of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the literal original diagonal is continuous, and the sum of its actual partial derivatives is independently continuous on each positive strip. Its right derivative was proved from the original quotient split. The right-derivative FTC therefore gives the actual derivative on the entire closed physical strip, including its upper endpoint. -/
theorem kernelDiagonal_hasDerivWithinAt {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => kernelDiagonal a ha (halfParameterClamp x))
      (diagonalSlopeRows ha hd (hdt.trans t.property.2) ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩)
      (Icc d (1/2)) (t:ℝ) := by
  -- The same actual diagonal and the same original partial derivatives are retained when the right-derivative endpoint theorem is applied.
  have hds := hdt.trans t.property.2
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds,continuous_projIcc⟩
  let g := (diagonalSlopeRows ha hd hds).comp P
  have he (x : ℝ) (hx : x∈Icc d (1/2)) : g x=diagonalSlopeRows ha hd hds ⟨x,hx⟩ := by
    change diagonalSlopeRows ha hd hds (Set.projIcc d (1/2) hds x)=_
    rw [Set.projIcc_of_mem hds hx]
  have hright (x : ℝ) (hx : x∈Ico d (1/2)) :
      HasDerivWithinAt (fun y : ℝ => kernelDiagonal a ha (halfParameterClamp y)) (g x) (Ici x) x := by
    rw [he x ⟨hx.1,hx.2.le⟩]
    exact kernelDiagonal_hasDerivWithinAt_right ha hd ⟨x,⟨(hd.trans_le hx.1).le,hx.2.le⟩⟩ hx.1 hx.2
  have h := continuous_hasDerivWithinAt_of_right
    ((kernelDiagonal a ha).continuous.comp halfParameterClamp.continuous) g.continuous ⟨hdt,t.property.2⟩ hright
  rw [he (t:ℝ) ⟨hdt,t.property.2⟩] at h
  exact h

end
end jacobi.GelfandLevitan
