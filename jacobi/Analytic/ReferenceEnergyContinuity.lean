import jacobi.Analytic.ReferenceEnergyAnalytic

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Joint continuity of the original energy series, including zero frequency
and the singular spatial endpoint. The estimates concern the defining
coefficients themselves and require no continuous square-root choice.
Use: supplies the continuous terms in the normal energy series used for the GL kernel.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original energy coefficients are continuous under simultaneous changes of order and energy.
Use: supplies the continuous terms in the normal energy series used for the GL kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the numerator is a finite product of polynomials, while the actual denominator rising factorial is nonzero at positive real part. -/
theorem energyCoefficient_comp_continuousAt {T : Type*} [TopologicalSpace T]
    {A Z : T → ℂ} {p : T} (hA : ContinuousAt A p) (hZ : ContinuousAt Z p)
    (ha : 0<(gamma (A p)).re) (n : ℕ) :
    ContinuousAt (fun u => energyCoefficient (A u) n (Z u)) p := by
  -- Only the genuine denominator is inverted; no auxiliary frequency is selected.
  have hg : ContinuousAt (fun u => gamma (A u)+1/2) p := by unfold gamma; fun_prop
  have hd := (ascPochhammer ℂ n).continuous.continuousAt.comp
    (f := fun u => gamma (A u)+1/2) hg
  have hp : 0<(gamma (A p)+1/2).re := by norm_num; linarith
  have hn : ContinuousAt (fun u => (n.factorial:ℂ)⁻¹*
      (∏ j∈Finset.range n,((gamma (A u)+j)^2-(Z u-besselCoefficient (A u))/(Real.pi:ℂ)^2))) p := by
    unfold gamma besselCoefficient
    fun_prop
  exact hn.mul (hd.inv₀ (jacobi.Reference.Hypergeometric.pochhammer_ne_zero hp n))

/-- The original energy core is jointly continuous under continuous order, energy and Gauss-coordinate maps.
Use: proves joint continuity of the actual GL reference factors, including the energy branch point.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: retain a positive exponent margin, bounded shifted energy and a Gauss radius below one on a common neighborhood. The proved coefficient comparison gives a summable positive Gauss majorant, so the continuous terms converge uniformly there. -/
theorem energyCore_comp_continuousAt {T : Type*} [TopologicalSpace T]
    {A Z X : T → ℂ} {p : T} (hA : Continuous A) (hZ : Continuous Z) (hX : Continuous X)
    (ha : 0<(gamma (A p)).re) (hx : ‖X p‖<1) :
    ContinuousAt (fun u => energyCore (A u) (Z u) (X u)) p := by
  -- One neighborhood controls all variables and every term of the original series.
  have hg : Continuous (fun u => gamma (A u)) := by unfold gamma; fun_prop
  have he : Continuous (fun u => Z u-besselCoefficient (A u)) := by unfold besselCoefficient; fun_prop
  let δ : ℝ := (gamma (A p)).re/2
  let G : ℝ := ‖gamma (A p)‖+1
  let E : ℝ := ‖Z p-besselCoefficient (A p)‖+1
  let r : ℝ := (‖X p‖+1)/2
  let D : ℝ := G+(E+1)/Real.pi+1
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hG : 0<G := by dsimp [G]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; linarith
  have hm : ∀ᶠ u in 𝓝 p,δ<(gamma (A u)).re :=
    (Complex.continuous_re.continuousAt.comp hg.continuousAt).eventually_const_lt (by dsimp [δ]; linarith)
  have hgm : ∀ᶠ u in 𝓝 p,‖gamma (A u)‖<G := hg.continuousAt.norm.eventually_lt_const (by dsimp [G]; linarith)
  have hem : ∀ᶠ u in 𝓝 p,‖Z u-besselCoefficient (A u)‖<E :=
    he.continuousAt.norm.eventually_lt_const (by dsimp [E]; linarith)
  have hxm : ∀ᶠ u in 𝓝 p,‖X u‖<r := hX.continuousAt.norm.eventually_lt_const (by dsimp [r]; linarith)
  obtain ⟨U,hUsub,hUopen,hpU⟩ := eventually_nhds_iff.mp (hm.and (hgm.and (hem.and hxm)))
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖*r^n
  have hM : Summable M := by
    have hh := jacobi.Reference.Hypergeometric.summable_norm
      (u := (D:ℂ)) (v := (D:ℂ)) (c := (δ:ℂ)) (x := (r:ℂ))
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; exact hr1)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hterms (n : ℕ) : ContinuousOn (fun u => energyCoefficient (A u) n (Z u)*(X u)^n) U := by
    intro u hu
    exact ((energyCoefficient_comp_continuousAt hA.continuousAt hZ.continuousAt
      (hδ.trans (hUsub u hu).1) n).mul (hX.continuousAt.pow n)).continuousWithinAt
  have hbound (n : ℕ) (u : T) (hu : u∈U) :
      ‖energyCoefficient (A u) n (Z u)*(X u)^n‖≤M n := by
    obtain ⟨hmargin,hgu,heu,hxu⟩ := hUsub u hu
    have hc : δ≤(gamma (A u)+1/2).re := by norm_num; linarith
    rw [norm_mul,norm_pow]
    exact mul_le_mul (energyCoefficient_bound hG hδ hE hgu.le hc heu.le n)
      (pow_le_pow_left₀ (norm_nonneg _) hxu.le n) (by positivity) (norm_nonneg _)
  have hs := (tendstoUniformlyOn_tsum hM hbound).continuousOn
    (Eventually.frequently (Eventually.of_forall (fun s => continuousOn_finsetSum s (fun n _ => hterms n))))
  exact hs.continuousAt (hUopen.mem_nhds hpU)

/-- The genuine reference solution is jointly continuous in order, energy and physical position throughout the physical convergence interval.
Use: gives joint continuity and compact bounds for the actual analytic GL summands, including every finite spectral index.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original sine power is jointly continuous at positive-real-part exponent, including its zero base. Multiply it by the normally convergent energy core at the original continuous Gauss coordinate. -/
theorem solution_joint_continuous {a z : ℂ} {t : ℝ}
    (ha : 0<(gamma a).re) (ht : t∈Ico 0 1) :
    ContinuousAt (fun p : ℂ × ℂ × ℝ => solution p.1 p.2.1 p.2.2) (a,z,t) := by
  -- Normal convergence handles the energy branch point and the physical endpoint simultaneously.
  have hg : Continuous gamma := by unfold gamma; fun_prop
  have hx : Continuous (fun t : ℝ => (jacobi.Reference.coordinate t:ℂ)) := by
    apply Complex.continuous_ofReal.comp
    exact continuous_iff_continuousAt.mpr (fun s => (jacobi.Reference.coordinate_hasDerivAt s).continuousAt)
  have hc := energyCore_comp_continuousAt
    (A := fun p : ℂ × ℂ × ℝ => p.1) (Z := fun p => p.2.1)
    (X := fun p => (jacobi.Reference.coordinate p.2.2:ℂ)) (p := (a,z,t))
    continuous_fst (continuous_fst.comp continuous_snd)
    (hx.comp (continuous_snd.comp continuous_snd)) ha
    (jacobi.Reference.coordinate_norm_lt_one_of_nonneg ht)
  have hw := (Complex.continuousAt_cpow_of_re_pos
    (p := (((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ),gamma a))
    (Or.inl (by simpa only [Complex.ofReal_re] using sineBase_nonneg ht)) ha).comp_of_eq
    (show ContinuousAt (fun p : ℂ × ℂ × ℝ =>
      (((Real.sin (Real.pi*p.2.2)/Real.pi:ℝ):ℂ),gamma p.1)) (a,z,t) by fun_prop) rfl
  exact hw.mul hc

end
end jacobi.ComplexReference
