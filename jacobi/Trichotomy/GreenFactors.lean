import jacobi.Trichotomy.GreenColumns

/-!
Article: jacobi, Proposition 2.2.
Two fixed columns outside a local interval give positive C2 Green factors.
The actual unit source fixes their Wronskian to one, without constructing
or classifying solutions at either singular endpoint.
Source: the one-dimensional Markov identity and one-sided derivative uniqueness.
Use: GreenExponential identifies their logarithmic ratio with the original
intrinsic coordinate and obtains the exact exponential kernel formula.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- Local equality on either one-sided interval determines the actual slope.
Use: targetGreen_local_factors compares the two classical factor branches
with the already normalized actual point-source model at its source.
Article: jacobi, Proposition 2.2.
Source: uniqueness of the one-sided derivative.
Proof: transfer one derivative through relative local equality and compare
the resulting two within derivatives on the same unique-differentiation set. -/
theorem slope_eq_on_side {f g : ℝ → ℝ} {df dg l r c : ℝ} {S : Set ℝ}
    (hc : c∈Ioo l r) (hcs : c∈S) (hS : UniqueDiffWithinAt ℝ S c)
    (hf : HasDerivAt f df c) (hg : HasDerivAt g dg c)
    (he : ∀ s∈Ioo l r,s∈S → f s=g s) : df=dg := by
  have he' : f=ᶠ[𝓝[S] c] g := by
    change ∀ᶠ s in 𝓝[S] c,f s=g s
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Ioo.mem_nhds hc] with s hs
    exact he s hs
  exact (hf.hasDerivWithinAt.derivWithin hS).symm.trans
    ((hg.hasDerivWithinAt.congr_of_eventuallyEq he' (he c hc hcs)).derivWithin hS)

/-- The true original Green kernel in real coordinates, with continuous
closed-interval projection outside the physical domain.
Use: targetGreen_local_factors and targetGreen_exponential concern its
unchanged original values at arbitrary physical interior points.
Article: jacobi, Proposition 2.2.
-/
def physicalGreenKernel (a : ℝ) (ha : -1<a) (t s : ℝ) : ℝ :=
  targetGreenKernel a ha (projIcc 0 1 (by norm_num) t) (projIcc 0 1 (by norm_num) s)

/-- Real-coordinate Green values agree with the original subtype kernel.
Use: transfers the already proved positivity and Markov identity to local
factor calculations, without changing any original normalization.
Article: jacobi, Proposition 2.2.
Proof: the projection fixes both original physical points. -/
theorem physicalGreenKernel_eq (a : ℝ) (ha : -1<a) (t s : Interval) :
    physicalGreenKernel a ha t s=targetGreenKernel a ha t s := by
  simp only [physicalGreenKernel,projIcc_of_mem (by norm_num) t.property,
    projIcc_of_mem (by norm_num) s.property]

/-- Every interior subinterval has genuine positive C2 Green factors with
Wronskian exactly one, and their ordered product is the actual original kernel.
Use: the logarithmic factor ratio has derivative exactly 1/phi_alpha,
which proves the original exponential Green-coordinate representation.
Article: jacobi, Proposition 2.2.
Proof: take the two exterior source columns at l and r. Their actual local
models are C2 on the interior, and Markov factorization gives the ordered
product. At each interior source the same product's two branch slopes
must differ by one, by the independently proved unit-source model. -/
theorem targetGreen_local_factors (a : ℝ) (ha : -1<a)
    {l r : ℝ} (hl : 0<l) (hr : r<1) (hlr : l<r) :
    ∃ L R : ℝ → ℝ,ContDiff ℝ 2 L ∧ ContDiff ℝ 2 R ∧
      (∀ s∈Ioo l r,0<L s ∧ 0<R s) ∧
      (∀ s∈Ioo l r,deriv L s*R s-L s*deriv R s=1) ∧
      ∀ s∈Ioo l r,∀ u∈Ioo l r,s≤u → physicalGreenKernel a ha s u=L s*R u := by
  let G := physicalGreenKernel a ha
  let li : Interval := ⟨l,⟨hl.le,(hlr.trans hr).le⟩⟩
  let ri : Interval := ⟨r,⟨(hl.trans hlr).le,hr.le⟩⟩
  have hpos (s u : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1) : 0<G s u := by
    simpa only [G,physicalGreenKernel,projIcc_of_mem (by norm_num) ⟨hs.1.le,hs.2.le⟩,
      projIcc_of_mem (by norm_num) ⟨hu.1.le,hu.2.le⟩] using targetGreen_pos a ha s u hs hu
  have hsym (s u : ℝ) : G s u=G u s := targetGreenKernel_symmetric a ha _ _
  have hin (s : ℝ) (hs : s∈Ioo l r) : s∈Ioo (0:ℝ) 1 :=
    ⟨hl.trans hs.1,hs.2.trans hr⟩
  have hl0 : l∈Ioo (0:ℝ) 1 := ⟨hl,hlr.trans hr⟩
  have hr0 : r∈Ioo (0:ℝ) 1 := ⟨hl.trans hlr,hr⟩
  have hmark (s u v : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
      (hv : v∈Ioo (0:ℝ) 1) (hsu : s≤u) (huv : u≤v) :
      G s v*G u u=G s u*G u v := by
    simpa only [G,physicalGreenKernel,projIcc_of_mem (by norm_num) ⟨hs.1.le,hs.2.le⟩,
      projIcc_of_mem (by norm_num) ⟨hu.1.le,hu.2.le⟩,
      projIcc_of_mem (by norm_num) ⟨hv.1.le,hv.2.le⟩] using
        targetGreen_markov a ha s u v hs hu hv hsu huv
  have hcol (s : ℝ) (si : Interval) (he : (si:ℝ)=s) (hs : s∈Ioo (0:ℝ) 1) :
      targetGreenColumn a ha si=G s := by
    subst s
    funext u
    simp only [targetGreenColumn,G,physicalGreenKernel,projIcc_of_mem (by norm_num) si.property]
  -- Sources at l and r lie outside the local open interval. Their source
  -- corners disappear there, leaving two genuine global C2 representatives.
  obtain ⟨Fl,hFl,_,hFle⟩ := targetGreen_column_model a ha li hl hr hlr
  obtain ⟨Fr,hFr,_,hFre⟩ := targetGreen_column_model a ha ri hl hr hlr
  let L := fun s => Fr s/G l r
  let R := fun s => Fl s-(s-l)
  have hL (s : ℝ) (hs : s∈Ioo l r) : L s=G s r/G l r := by
    have he := hFre s hs
    rw [hcol r ri rfl hr0,max_eq_right (sub_nonpos.mpr hs.2.le),sub_zero] at he
    dsimp only [L]
    rw [← he,hsym r s]
  have hR (s : ℝ) (hs : s∈Ioo l r) : R s=G l s := by
    have he := hFle s hs
    rw [hcol l li rfl hl0,max_eq_left (sub_nonneg.mpr hs.1.le)] at he
    exact he.symm
  have hLc : ContDiff ℝ 2 L := hFr.div_const _
  have hRc : ContDiff ℝ 2 R := hFl.sub (contDiff_id.sub contDiff_const)
  have hprod (s u : ℝ) (hs : s∈Ioo l r) (hu : u∈Ioo l r) (hsu : s≤u) : G s u=L s*R u := by
    rw [hL s hs,hR u hu,div_mul_eq_mul_div]
    apply (eq_div_iff (hpos l r hl0 hr0).ne').mpr
    apply mul_right_cancel₀ (hpos u r (hin u hu) hr0).ne'
    have h1 := hmark s u r (hin s hs) (hin u hu) hr0 hsu hu.2.le
    have h2 := hmark l u r hl0 (hin u hu) hr0 hu.1.le hu.2.le
    linear_combination G s r*h2-G l r*h1
  refine ⟨L,R,hLc,hRc,?_,?_,fun s hs u hu hsu => hprod s u hs hu hsu⟩
  · intro s hs
    rw [hL s hs,hR s hs]
    exact ⟨div_pos (hpos s r (hin s hs) hr0) (hpos l r hl0 hr0),hpos l s hl0 (hin s hs)⟩
  · intro c hc
    let ci : Interval := ⟨c,⟨(hin c hc).1.le,(hin c hc).2.le⟩⟩
    obtain ⟨F,hF,_,hFe⟩ := targetGreen_column_model a ha ci hl hr hlr
    have hF' := (hF.differentiable (by norm_num) c).hasDerivAt
    have hL' := (hLc.differentiable (by norm_num) c).hasDerivAt
    have hR' := (hRc.differentiable (by norm_num) c).hasDerivAt
    -- The left and right branches must have the slopes of the same unit
    -- source model. Their difference fixes W=1, rather than an unknown scale.
    have heL : deriv F c=deriv L c*R c := slope_eq_on_side hc self_mem_Iic
        (uniqueDiffWithinAt_Iic c) hF' (hL'.mul_const (R c)) (by
      intro s hs hsc
      have hh := hFe s hs
      rw [hcol c ci rfl (hin c hc),max_eq_right (sub_nonpos.mpr hsc),sub_zero,
        hsym c s,hprod s c hs hc hsc] at hh
      exact hh.symm)
    have heR : deriv F c-1=L c*deriv R c := slope_eq_on_side hc self_mem_Ici
        (uniqueDiffWithinAt_Ici c) (hF'.sub ((hasDerivAt_id c).sub_const c))
        (hR'.const_mul (L c)) (by
      intro s hs hcs
      have hh := hFe s hs
      rw [hcol c ci rfl (hin c hc),max_eq_left (sub_nonneg.mpr hcs),
        hprod c s hc hs hcs] at hh
      exact hh.symm)
    linarith

end
end jacobi.Trichotomy
