import jacobi.GelfandLevitan.ReflectionRegularity
import jacobi.GelfandLevitan.TargetPotential
import jacobi.GelfandLevitan.MidpointNeumann
import jacobi.GelfandLevitan.FullWaveMaps

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original reflected target waves are C2 across the midpoint and solve
the original Schrodinger equation there as well as on both open halves.
All three matching values come from the proved exact characteristic
boundary conditions and the actual original half-domain ODE.
Use: fullWavePhysical is its actual normalized real representative, and reflectedWave_ODE proves its genuine differential equation across the midpoint.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original unnormalized reflected target wave in real physical coordinates.
Use: fullWavePhysical is its actual normalized real representative, and reflectedWave_ODE proves its genuine differential equation across the midpoint.
Article: jacobi, Theorem 2.1.
-/
def reflectedWave (a : ℝ) (ha : -1<a) (n : ℕ) : ℝ → ℂ :=
  reflectMidpoint ((-1:ℂ)^n)
    (fun x => transformedSolution a ha (halfParameterClamp x) (jacobi.Bessel.sigma a ha n:ℂ))

/-- The normalized full target wave as an actual real-coordinate function.
Use: fullWavePhysical_eq_map connects genuine classical derivatives with the already proved continuous Hilbert-basis representatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def fullWavePhysical (a : ℝ) (ha : -1<a) (n : ℕ) (t : ℝ) : ℝ :=
  targetWaveScale a ha n*(reflectedWave a ha n t).re

/-- The genuine original slope at the midpoint is independent of the strip used to compute it.
Use: reflectedWave_strip applies the exact original Neumann condition to every actual positive strip.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: transfer both independently proved original derivatives to the actual midpoint left neighborhood. Uniqueness of that derivative gives the equality. -/
theorem transformedSlope_midpoint {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) :
    transformedSlopeRows ha hd z ⟨1/2,⟨hds.le,le_rfl⟩⟩=midpointSlope a ha z := by
  have h1 := (transformedSolution_hasDerivWithinAt ha hd z halfMidpoint hds.le).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE hds)
  have h2 := (midpointSlope_hasDerivWithinAt a ha z).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE (by norm_num : (1/4:ℝ)<1/2))
  exact (h1.derivWithin (uniqueDiffWithinAt_Iic _)).symm.trans
    (h2.derivWithin (uniqueDiffWithinAt_Iic _))

/-- The actual complex midpoint value has exactly its original reflection parity.
Use: reflectedWave_strip glues the original wave values and their actual ODE second derivatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the even sign is one; the genuine odd midpoint value is zero by the exhaustive actual Dirichlet zero theorem. -/
theorem midpointValue_parity (a : ℝ) (ha : -1<a) (n : ℕ) :
    midpointValue a ha (jacobi.Bessel.sigma a ha n:ℂ)=
      (-1:ℂ)^n*midpointValue a ha (jacobi.Bessel.sigma a ha n:ℂ) := by
  obtain ⟨k,hk|hk⟩ := Nat.even_or_odd' n <;> subst n
  · simp only [pow_mul,neg_one_sq,one_pow,one_mul]
  · have h := (midpointValue_zero_iff a ha _).mpr ⟨k,rfl⟩
    change midpointValue a ha (jacobi.Bessel.sigma a ha (2*k+1):ℂ)=0 at h
    rw [h,mul_zero]

/-- The actual complex midpoint slope has exactly the opposite reflection parity.
Use: reflectedWave_strip constructs a genuine two-sided first derivative at the midpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the even midpoint slope is zero by the proved exact Neumann theorem; the odd negative reflection sign cancels. -/
theorem midpointSlope_parity (a : ℝ) (ha : -1<a) (n : ℕ) :
    midpointSlope a ha (jacobi.Bessel.sigma a ha n:ℂ)=
      -((-1:ℂ)^n)*midpointSlope a ha (jacobi.Bessel.sigma a ha n:ℂ) := by
  obtain ⟨k,hk|hk⟩ := Nat.even_or_odd' n <;> subst n
  · have h := midpoint_neumann_at_spectrum a ha k
    change midpointSlope a ha (jacobi.Bessel.sigma a ha (2*k):ℂ)=0 at h
    rw [h,mul_zero]
  · simp only [pow_add,pow_mul,neg_one_sq,one_pow,pow_one,one_mul,neg_neg]

/-- Every genuine reflected target wave is C2 on each symmetric positive strip; its actual second derivative is the original target ODE coefficient times that same wave.
Use: reflectedWave_contDiffOn_two and reflectedWave_ODE localize these actual conclusions to the entire original physical interior, including its midpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: use the independently proved actual first and second half-domain derivatives. Their midpoint values satisfy the genuine parity identities, and the second derivative has the value parity by the original ODE. Ordinary two-sided derivative gluing therefore applies twice. The physical fold identifies each reflected ODE coefficient with the same original symmetric potential. -/
theorem reflectedWave_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (n : ℕ) :
    ContDiffOn ℝ 2 (reflectedWave a ha n) (Ioo d (1-d)) ∧
      ∀ t∈Ioo d (1-d),
        HasDerivAt (deriv (reflectedWave a ha n))
          ((((targetPotential a ha t:ℝ):ℂ)-(jacobi.Bessel.sigma a ha n:ℂ))*
            reflectedWave a ha n t) t := by
  -- The local auxiliary slope and acceleration are actual clamped original strip functions, whose derivative identities were proved independently.
  let z : ℂ := jacobi.Bessel.sigma a ha n
  let ε : ℂ := (-1)^n
  let f := fun x => transformedSolution a ha (halfParameterClamp x) z
  let g := stripExtension hds.le (transformedSlopeRows ha hd z)
  let H := (stripComplex (transformedPotentialStrip a ha hd hds.le)-ContinuousMap.const _ z)*
    transformedSolutionStrip a ha hd z
  let h := stripExtension hds.le H
  have hD (x : ℝ) (hx : x∈Icc d (1/2)) : HasDerivWithinAt f (g x) (Icc d (1/2)) x := by
    rw [show x=(⟨x,hx⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
    exact transformedSolution_hasDerivWithinAt ha hd z ⟨x,⟨(hd.trans_le hx.1).le,hx.2⟩⟩ hx.1
  have hDD (x : ℝ) (hx : x∈Icc d (1/2)) : HasDerivWithinAt g (h x) (Icc d (1/2)) x := by
    rw [show x=(⟨x,hx⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
    exact transformedSolution_ODE_strip a ha hd hds z ⟨x,hx⟩
  have hfM : f (1/2)=midpointValue a ha z := by
    change transformedSolution a ha (halfParameterClamp (1/2)) z=transformedSolution a ha halfMidpoint z
    rw [show halfParameterClamp (1/2)=halfMidpoint from Set.projIcc_of_mem (by norm_num) (by norm_num)]
  have hf0 : f (1/2)=ε*f (1/2) := by
    rw [hfM]
    exact midpointValue_parity a ha n
  have hg0 : g (1/2)= -ε*g (1/2) := by
    have he : g (1/2)=midpointSlope a ha z := by
      rw [show (1/2:ℝ)=(⟨1/2,⟨hds.le,le_rfl⟩⟩:ClosedStrip d (1/2)).val from rfl,
        stripExtension_value,transformedSlope_midpoint ha hd hds]
    rw [he]
    exact midpointSlope_parity a ha n
  have hh0 : h (1/2)=ε*h (1/2) := by
    rw [show (1/2:ℝ)=(⟨1/2,⟨hds.le,le_rfl⟩⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
    change (_-z)*midpointValue a ha z=ε*((_-z)*midpointValue a ha z)
    linear_combination (_-z)*(midpointValue_parity a ha n)
  have hG (x : ℝ) (hx : x∈Ioo d (1-d)) := reflectMidpoint_hasDerivAt hds ε hD hf0 hg0 hx
  have hH (x : ℝ) (hx : x∈Ioo d (1-d)) :
      HasDerivAt (reflectMidpoint (-ε) g) (reflectMidpoint ε h x) x := by
    simpa only [neg_neg] using reflectMidpoint_hasDerivAt hds (-ε) hDD hg0 (by simpa only [neg_neg] using hh0) hx
  refine ⟨reflection_contDiffOn_two hds ε h.continuous hD hDD hf0 hg0 hh0,?_⟩
  intro t ht
  have hder : deriv (reflectedWave a ha n)=ᶠ[𝓝 t] reflectMidpoint (-ε) g := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (hG x hx).deriv
  have hacc : reflectMidpoint ε h t=((targetPotential a ha t:ℂ)-z)*reflectedWave a ha n t := by
    -- The actual strip ODE coefficient agrees with the single symmetric physical potential on both halves.
    have hval (x : ℝ) (hx : x∈Ioc d (1/2)) :
        h x=((targetPotential a ha x:ℂ)-z)*f x := by
      rw [show x=(⟨x,⟨hx.1.le,hx.2⟩⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
      rw [targetPotential_strip ha hd hds.le hx]
      change (_-z)*transformedSolution a ha (derivativeStripInclusion hd ⟨x,⟨hx.1.le,hx.2⟩⟩) z=
        (_-z)*transformedSolution a ha (halfParameterClamp x) z
      rw [show halfParameterClamp x=derivativeStripInclusion hd ⟨x,⟨hx.1.le,hx.2⟩⟩ from
        halfParameterClamp_strip hd ⟨x,⟨hx.1.le,hx.2⟩⟩]
      rfl
    by_cases hp : t≤1/2
    · simpa only [reflectedWave,reflectMidpoint,ite_eq_left hp] using hval t ⟨ht.1,hp⟩
    · have hr : 1-t∈Ioc d (1/2) := ⟨by linarith [ht.2],by linarith [lt_of_not_ge hp]⟩
      simp only [reflectMidpoint,reflectedWave,ite_eq_right hp]
      change ε*h (1-t)=((targetPotential a ha t:ℂ)-z)*(ε*f (1-t))
      rw [hval (1-t) hr,targetPotential_reflection]
      ring
  rw [← hacc]
  exact (hH t ht).congr_of_eventuallyEq hder

end
end jacobi.GelfandLevitan
