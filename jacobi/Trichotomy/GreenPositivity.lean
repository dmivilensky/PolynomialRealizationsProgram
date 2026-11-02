import jacobi.Trichotomy.GreenMarkov
import jacobi.Analysis.MarkovKernel

/-!
Article: jacobi, Proposition 2.2.
The actual continuous full target Green kernel has a strictly positive
diagonal by its original spectral profile. The exact finite-to-continuum
Markov identity and connectedness propagate nonvanishing to every entry.
Use: GreenFactors constructs positive genuine Green factors and identifies
the original intrinsic-coordinate kernel without assuming positivity.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
set_option backward.isDefEq.respectTransparency false

/-- The full original target Green kernel is strictly positive at every pair of physical interior points.
Use: supplies the positive factorization and exponential-coordinate representation in Proposition 2.2 for every alpha>-1.
Article: jacobi, Proposition 2.2.
Proof: restrict the true continuous kernel to the connected physical interior. Its diagonal is half the independently proved positive original profile. The inherited exact Markov identity makes nonvanishing transitive. The clopen-class theorem makes every entry nonzero; the inherited nonnegativity makes it strictly positive. -/
theorem targetGreen_pos (a:ℝ) (ha:-1<a) (t s:ℝ)
    (ht:t∈Ioo (0:ℝ) 1) (hs:s∈Ioo (0:ℝ) 1) :
    0<targetGreenKernel a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ ⟨s,⟨hs.1.le,hs.2.le⟩⟩ := by
  -- Both strict positivity inputs are proved for the unchanged original spectral kernel and its actual finite inverse limits.
  let X := Ioo (0:ℝ) 1
  have : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_Ioo
  let e : X→Interval := fun x => ⟨x,⟨x.property.1.le,x.property.2.le⟩⟩
  let G : X→X→ℝ := fun x y => targetGreenKernel a ha (e x) (e y)
  have hc : Continuous (fun p:X × X => G p.1 p.2) := by
    apply (targetGreenKernelMap a ha).continuous.comp
    exact (continuous_subtype_val.comp continuous_fst).subtype_mk _ |>.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hsym (x y:X) : G x y=G y x := targetGreenKernel_symmetric a ha _ _
  have hd (x:X) : G x x≠0 := by
    have hp := persymmetricProfile_pos a ha (e x) x.property
    have he := targetGreen_diagonal a ha (e x)
    change targetGreenKernel a ha (e x) (e x)≠0
    linarith
  have hm (x y z:X) (hxy:x≤y) (hyz:y≤z) : G x z*G y y=G x y*G y z :=
    targetGreen_markov a ha x y z x.property y.property z.property hxy hyz
  have hn := jacobi.Analysis.continuous_kernel_nonzero hc hsym hd
    (jacobi.Analysis.markov_nonzero_transitive hsym hd hm) (⟨t,ht⟩:X) (⟨s,hs⟩:X)
  exact lt_of_le_of_ne (targetGreen_nonneg a ha t s ht hs) (Ne.symm hn)

end
end jacobi.Trichotomy
