import jacobi.GelfandLevitan.ReflectedWaveEquation

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual normalized full Hilbert-basis representatives are classical C2
solutions on the entire physical interior. Their genuine ordinary second
derivatives give exactly the printed Schrodinger expression, including at
the midpoint. No smooth representative or differential identity is assumed.
Use: reflectedWave_contDiffOn_two and reflectedWave_ODE localize the independently proved actual midpoint-gluing theorem.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every physical interior point belongs to a genuine symmetric strip with strictly positive lower endpoint.
Use: reflectedWave_contDiffOn_two and reflectedWave_ODE localize the independently proved actual midpoint-gluing theorem.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: take half the smaller of the two positive endpoint distances. -/
theorem symmetricStrip_exists {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ∃ d:ℝ,0<d ∧ d<(1/2:ℝ) ∧ t∈Ioo d (1-d) := by
  have hp := physicalFold_mem ht
  refine ⟨min t (1-t)/2,by linarith [hp.1],by linarith [hp.1,hp.2],?_,?_⟩
  · linarith [min_le_left t (1-t),hp.1]
  · linarith [min_le_right t (1-t),hp.1]

/-- The genuine reflected original target wave is C2 throughout the original physical interior, including the midpoint.
Use: fullWavePhysical_contDiffOn_two transfers this actual regularity to the normalized real Hilbert-basis representatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: every interior point has a positive symmetric strip on which the true first and second derivatives have been glued. Locality of the community C2 predicate gives the full assertion. -/
theorem reflectedWave_contDiffOn_two (a : ℝ) (ha : -1<a) (n : ℕ) :
    ContDiffOn ℝ 2 (reflectedWave a ha n) (Ioo (0:ℝ) 1) := by
  intro t ht
  obtain ⟨d,hd,hdm,hdt⟩ := symmetricStrip_exists ht
  exact (((reflectedWave_strip a ha hd hdm n).1 t hdt).contDiffAt
    (isOpen_Ioo.mem_nhds hdt)).contDiffWithinAt

/-- The actual complex reflected wave has its genuine ordinary second derivative prescribed by the original full target equation everywhere inside the physical interval.
Use: fullWavePhysical_equation proves the actual real normalized Schrodinger equation and targetOperator_differential identifies the true spectral operator action.
Article: jacobi, Theorem 2.1.
Proof: specialize the independently proved genuine strip second derivative on a symmetric strip containing the point; its actual coefficient is the globally defined original target potential. -/
theorem reflectedWave_ODE (a : ℝ) (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (reflectedWave a ha n))
      (((targetPotential a ha t:ℂ)-(jacobi.Bessel.sigma a ha n:ℂ))*reflectedWave a ha n t) t := by
  obtain ⟨d,hd,hdm,hdt⟩ := symmetricStrip_exists ht
  exact (reflectedWave_strip a ha hd hdm n).2 t hdt

/-- The original normalized real target wave is C2 on the entire physical interior.
Use: finite target spectral combinations have genuine classical second derivatives, so the spectral realization acts as the original differential expression on their span.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine complex reflected wave is C2; real-part projection and the unchanged original normalization preserve this regularity. -/
theorem fullWavePhysical_contDiffOn_two (a : ℝ) (ha : -1<a) (n : ℕ) :
    ContDiffOn ℝ 2 (fullWavePhysical a ha n) (Ioo (0:ℝ) 1) :=
  contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (reflectedWave_contDiffOn_two a ha n))

/-- The actual full normalized wave has its true derivative as the normalized real part of the original complex reflected derivative.
Use: fullWavePhysical_second_derivative differentiates this genuine first-derivative identity locally in the physical interior.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the chain rule for the real-part continuous linear map.
Proof: C2 regularity supplies the actual first derivative; real-part projection and multiplication by the genuine constant give the displayed original derivative. -/
theorem fullWavePhysical_derivative (a : ℝ) (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fullWavePhysical a ha n)
      (targetWaveScale a ha n*(deriv (reflectedWave a ha n) t).re) t := by
  have h := (((reflectedWave_contDiffOn_two a ha n) t ht).contDiffAt
    (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num : (2:WithTop ℕ∞)≠0)
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).const_mul _

/-- The actual normalized real wave has the genuine original target second derivative everywhere in the physical interior, including at the midpoint.
Use: fullWavePhysical_equation and targetOperator_differential use true ordinary derivatives, without substituting a separately defined acceleration function.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual first derivative agrees locally with the normalized real part of the original reflected slope. Differentiate that true slope using the proved original complex ODE; its coefficient is real, giving the unchanged normalized real equation. -/
theorem fullWavePhysical_second_derivative (a : ℝ) (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (fullWavePhysical a ha n))
      ((targetPotential a ha t- jacobi.Bessel.sigma a ha n)*fullWavePhysical a ha n t) t := by
  -- Derivative uniqueness is used only inside the genuine physical open interval, where the actual original C2 wave has already been proved.
  have he : deriv (fullWavePhysical a ha n)=ᶠ[𝓝 t]
      (fun x => targetWaveScale a ha n*(deriv (reflectedWave a ha n) x).re) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (fullWavePhysical_derivative a ha n hx).deriv
  have h := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (reflectedWave_ODE a ha n ht)).const_mul (targetWaveScale a ha n)).congr_of_eventuallyEq he
  convert h using 1
  dsimp only [Complex.reCLM_apply,fullWavePhysical]
  simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_self,zero_mul,sub_zero]
  ring

/-- The original full target wave satisfies precisely the printed classical Schrodinger equation at every interior point.
Use: targetOperator_differential combines these actual equations with the genuine spectral action on arbitrary finite target combinations.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: rearrange the independently proved true second-derivative formula. -/
theorem fullWavePhysical_equation (a : ℝ) (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    -deriv (deriv (fullWavePhysical a ha n)) t+targetPotential a ha t*fullWavePhysical a ha n t=
      jacobi.Bessel.sigma a ha n*fullWavePhysical a ha n t := by
  rw [(fullWavePhysical_second_derivative a ha n ht).deriv]
  ring

/-- The genuine real-coordinate target wave is exactly the previously constructed continuous closed-interval representative of the full original Hilbert basis.
Use: targetOperator_differential connects classical derivatives to the actual unbounded operator on L2 quotient vectors.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: on either physical half the real coordinate clamp equals the original physical half clamp. The complex reflection sign is real, so taking its real part preserves the literal original reflected-wave formula. -/
theorem fullWavePhysical_eq_map (a : ℝ) (ha : -1<a) (n : ℕ) (t : Interval) :
    fullWavePhysical a ha n t=fullWaveMap a ha n t := by
  -- The two continuous functions use the same actual u and normalization; only their coordinate domains differ.
  have hl (s : Interval) : halfParameterClamp (s:ℝ)=halfClamp s := by
    apply Subtype.ext
    change max 0 (min (1/2) (s:ℝ))=min (s:ℝ) (1/2)
    rw [min_comm,max_eq_right (le_min s.property.1 (by norm_num))]
  by_cases ht : (t:ℝ)≤1/2
  · simp only [fullWavePhysical,reflectedWave,reflectMidpoint,fullWaveMap,ContinuousMap.coe_mk,
      ite_eq_left ht,transformedRealWave,hl]
  · have hr : halfParameterClamp (1-(t:ℝ))=halfClamp (physicalReflection t) :=
      hl (physicalReflection t)
    have hs : (-1:ℂ)^n=(((-1:ℝ)^n:ℝ):ℂ) := by norm_cast
    simp only [fullWavePhysical,reflectedWave,reflectMidpoint,fullWaveMap,ContinuousMap.coe_mk,
      ite_eq_right ht,transformedRealWave,hr,hs,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end
end jacobi.GelfandLevitan
