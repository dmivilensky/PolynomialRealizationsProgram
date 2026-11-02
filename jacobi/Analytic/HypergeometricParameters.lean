import jacobi.Reference.HypergeometricBounds

/-!
Article: jacobi, Lemma C.1.
The original Gauss series depends holomorphically on all its parameters
when the denominator parameter has positive real part. Unlike the earlier
fixed-real-order estimates, the denominator now varies as well.
Source: Gauss's defining series, DLMF 15.2.1, and Weierstrass' theorem.
Use: controls the moving denominator of the complex-order reference series.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Complex Set Polynomial Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A positive lower bound for the real part gives the corresponding positive rising-factorial lower norm bound.
Use: controls the moving denominator of the complex-order reference series.
Article: jacobi, Lemma C.1.
Proof: every successive complex factor has norm at least its real part,
which is at least the positive comparison parameter plus the natural index.
Multiply these bounds along the actual rising-factorial recurrence. -/
theorem pochhammer_norm_lower {c : ℂ} {δ : ℝ} (hδ : 0<δ) (hc : δ≤c.re) (n : ℕ) :
    (ascPochhammer ℝ n).eval δ≤‖(ascPochhammer ℂ n).eval c‖ := by
  -- Each denominator factor is estimated before forming its genuine finite product.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,norm_mul]
    apply mul_le_mul ih ?_ (by positivity) (norm_nonneg _)
    have hh := Complex.re_le_norm (c+(n:ℂ))
    simp only [Complex.add_re,Complex.natCast_re] at hh
    linarith

/-- Every rising factorial at a parameter with positive real part is nonzero.
Use: the moving reference coefficient denominators are holomorphic inverses.
Article: jacobi, Lemma C.1.
Proof: its norm is at least the strictly positive real rising factorial at that real part. -/
theorem pochhammer_ne_zero {c : ℂ} (hc : 0<c.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval c≠0 :=
  norm_pos_iff.mp ((ascPochhammer_pos n c.re hc).trans_le (pochhammer_norm_lower hc le_rfl n))

/-- The original Gauss coefficients have a fixed positive-parameter majorant even when their denominator parameter varies.
Use: one convergent community series controls the complex-order reference function on a full parameter neighborhood.
Article: jacobi, Lemma C.1.
Proof: bound both numerator rising factorials above by their positive
comparison values, and the denominator norm below by the positive
rising factorial at its real-part margin. Compare the exact coefficient norm products. -/
theorem coefficient_parameters_bound {u v c : ℂ} {D δ : ℝ} (hD : 0<D) (hδ : 0<δ)
    (hu : ‖u‖≤D) (hv : ‖v‖≤D) (hc : δ≤c.re) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient u v c n‖≤
      ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖ := by
  -- The actual positive-real-part denominator is retained throughout this estimate.
  have hp := pochhammer_norm_le hD hu n
  have hq := pochhammer_norm_le hD hv n
  have hd := pochhammer_norm_lower hδ hc n
  have hn (s : ℝ) (hs : 0<s) : ‖(ascPochhammer ℂ n).eval (s:ℂ)‖=(ascPochhammer ℝ n).eval s := by
    rw [pochhammer_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ascPochhammer_pos n s hs)]
  unfold ordinaryHypergeometricCoefficient
  simp only [norm_mul,norm_inv,hn D hD,hn δ hδ]
  have hf : 0≤‖(n.factorial:ℂ)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hP := (ascPochhammer_pos n D hD).le
  have hnum := mul_le_mul_of_nonneg_left (mul_le_mul hp hq (norm_nonneg _) hP) hf
  rw [← mul_assoc,← mul_assoc] at hnum
  exact mul_le_mul hnum (inv_anti₀ (ascPochhammer_pos n δ hδ) hd)
    (by positivity) (by positivity)

/-- Every genuine Gauss coefficient is analytic along analytic curves in all three parameters with positive denominator real part.
Use: the original complex-order reference series is a sum of actual holomorphic coefficients.
Article: jacobi, Lemma C.1.
Proof: rising factorials are polynomials; compose their actual evaluations
with the analytic parameter curves. The denominator rising factorial
does not vanish at the point, so its analytic inverse is legitimate. -/
theorem coefficient_comp_analytic {A B C : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p) (hC : AnalyticAt ℂ C p)
    (hc : 0<(C p).re) (n : ℕ) :
    AnalyticAt ℂ (fun u => ordinaryHypergeometricCoefficient (A u) (B u) (C u) n) p := by
  have hp := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hA
  have hq := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hB
  have hr := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hC
  exact ((analyticAt_const.mul hp).mul hq).mul (hr.inv (pochhammer_ne_zero hc n))

/-- The original Gauss function is analytic along every analytic curve in its parameters and spatial argument inside the genuine convergence disk.
Use: proves the complex-order reference solution's actual analytic dependence,
including terminating numerator parameters and moving denominator parameters.
Article: jacobi, Lemma C.1.
Proof: retain half the positive denominator margin and put the other
parameters and the spatial argument inside fixed norm bounds on one
neighborhood. The proved coefficient comparison gives one genuinely
summable Gauss majorant. Sum the analytic terms by the community
Weierstrass theorem and identify their sum with the original Gauss function. -/
theorem parameters_comp_analytic {A B C X : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p) (hC : AnalyticAt ℂ C p)
    (hX : AnalyticAt ℂ X p) (hc : 0<(C p).re) (hx : ‖X p‖<1) :
    AnalyticAt ℂ (fun u => ordinaryHypergeometric (A u) (B u) (C u) (X u)) p := by
  -- One actual parameter neighborhood controls every term of the genuine Gauss series.
  let δ : ℝ := (C p).re/2
  let D : ℝ := ‖A p‖+‖B p‖+1
  let r : ℝ := (‖X p‖+1)/2
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hD : 0<D := by dsimp [D]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; linarith
  have hcm : ∀ᶠ u in 𝓝 p,δ<(C u).re :=
    (Complex.continuous_re.continuousAt.comp hC.continuousAt).eventually_const_lt (by dsimp [δ]; linarith)
  have hAm : ∀ᶠ u in 𝓝 p,‖A u‖<D := hA.continuousAt.norm.eventually_lt_const (by dsimp [D]; linarith [norm_nonneg (B p)])
  have hBm : ∀ᶠ u in 𝓝 p,‖B u‖<D := hB.continuousAt.norm.eventually_lt_const (by dsimp [D]; linarith [norm_nonneg (A p)])
  have hXm : ∀ᶠ u in 𝓝 p,‖X u‖<r := hX.continuousAt.norm.eventually_lt_const (by dsimp [r]; linarith)
  obtain ⟨U,hUsub,hUopen,hpU⟩ := eventually_nhds_iff.mp
    ((hA.eventually_analyticAt.and hB.eventually_analyticAt).and
      ((hC.eventually_analyticAt.and hX.eventually_analyticAt).and (hcm.and (hAm.and (hBm.and hXm)))))
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖*r^n
  have hM : Summable M := by
    have hh := summable_norm (u := (D:ℂ)) (v := (D:ℂ)) (c := (δ:ℂ)) (x := (r:ℂ))
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; exact hr1)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hterms (n : ℕ) : DifferentiableOn ℂ
      (fun u => ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n) U := by
    intro u hu
    obtain ⟨⟨hAu,hBu⟩,⟨hCu,hXu⟩,hcu,hau,hbu,hxu⟩ := hUsub u hu
    exact ((coefficient_comp_analytic hAu hBu hCu (by linarith) n).mul (hXu.pow n)).differentiableAt.differentiableWithinAt
  have hbound (n : ℕ) (u : ℂ) (hu : u∈U) :
      ‖ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n‖≤M n := by
    obtain ⟨_,_,hcu,hau,hbu,hxu⟩ := hUsub u hu
    rw [norm_mul,norm_pow]
    exact mul_le_mul (coefficient_parameters_bound hD hδ hau.le hbu.le hcu.le n)
      (pow_le_pow_left₀ (norm_nonneg _) hxu.le n) (by positivity) (norm_nonneg _)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM hterms hUopen hbound
  have he : (fun u => ∑' n,ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n)=
      (fun u => ordinaryHypergeometric (A u) (B u) (C u) (X u)) := by
    funext u
    simp only [ordinaryHypergeometric_eq_tsum,smul_eq_mul]
  rw [he] at hd
  exact hd.analyticOnNhd hUopen p hpU

/-- The actual Gauss coefficients are continuous under simultaneous continuous changes of all their parameters at a positive-real-part denominator.
Use: supplies the continuous terms for joint continuity of the original complex-order reference series.
Article: jacobi, Lemma C.1.
Proof: polynomial evaluation is continuous and the actual denominator
rising factorial is nonzero, so all operations in the defining coefficient are continuous. -/
theorem coefficient_parameters_continuousAt {T : Type*} [TopologicalSpace T]
    {A B C : T → ℂ} {p : T} (hA : ContinuousAt A p) (hB : ContinuousAt B p)
    (hC : ContinuousAt C p) (hc : 0<(C p).re) (n : ℕ) :
    ContinuousAt (fun u => ordinaryHypergeometricCoefficient (A u) (B u) (C u) n) p := by
  have hp := (ascPochhammer ℂ n).continuous.continuousAt.comp hA
  have hq := (ascPochhammer ℂ n).continuous.continuousAt.comp hB
  have hr := (ascPochhammer ℂ n).continuous.continuousAt.comp hC
  exact ((continuousAt_const.mul hp).mul hq).mul (hr.inv₀ (pochhammer_ne_zero hc n))

/-- The original Gauss function is jointly continuous under all continuous parameter and spatial-argument changes inside its actual convergence disk.
Use: gives joint continuity of the complex-order reference functions,
including the singular physical endpoint after multiplying by its sine power.
Article: jacobi, Lemma C.1.
Proof: on a common neighborhood retain a positive denominator margin,
bounded numerator parameters and a spatial radius strictly below one.
The same proved summable Gauss coefficient majorant controls every
term, so the uniform sum of the continuous actual terms is continuous. -/
theorem parameters_comp_continuousAt {T : Type*} [TopologicalSpace T]
    {A B C X : T → ℂ} {p : T} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hX : Continuous X) (hc : 0<(C p).re) (hx : ‖X p‖<1) :
    ContinuousAt (fun u => ordinaryHypergeometric (A u) (B u) (C u) (X u)) p := by
  -- The comparison controls a product neighborhood, rather than only one parameter at a time.
  let δ : ℝ := (C p).re/2
  let D : ℝ := ‖A p‖+‖B p‖+1
  let r : ℝ := (‖X p‖+1)/2
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hD : 0<D := by dsimp [D]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; linarith
  have hcm : ∀ᶠ u in 𝓝 p,δ<(C u).re :=
    (Complex.continuous_re.continuousAt.comp hC.continuousAt).eventually_const_lt (by dsimp [δ]; linarith)
  have hAm : ∀ᶠ u in 𝓝 p,‖A u‖<D := hA.continuousAt.norm.eventually_lt_const (by dsimp [D]; linarith [norm_nonneg (B p)])
  have hBm : ∀ᶠ u in 𝓝 p,‖B u‖<D := hB.continuousAt.norm.eventually_lt_const (by dsimp [D]; linarith [norm_nonneg (A p)])
  have hXm : ∀ᶠ u in 𝓝 p,‖X u‖<r := hX.continuousAt.norm.eventually_lt_const (by dsimp [r]; linarith)
  obtain ⟨U,hUsub,hUopen,hpU⟩ := eventually_nhds_iff.mp (hcm.and (hAm.and (hBm.and hXm)))
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) (δ:ℂ) n‖*r^n
  have hM : Summable M := by
    have hh := summable_norm (u := (D:ℂ)) (v := (D:ℂ)) (c := (δ:ℂ)) (x := (r:ℂ))
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; exact hr1)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hterms (n : ℕ) : ContinuousOn
      (fun u => ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n) U := by
    intro u hu
    have hcu : 0<(C u).re := hδ.trans (hUsub u hu).1
    exact ((coefficient_parameters_continuousAt hA.continuousAt hB.continuousAt hC.continuousAt
      hcu n).mul (hX.continuousAt.pow n)).continuousWithinAt
  have hbound (n : ℕ) (u : T) (hu : u∈U) :
      ‖ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n‖≤M n := by
    obtain ⟨hcu,hau,hbu,hxu⟩ := hUsub u hu
    rw [norm_mul,norm_pow]
    exact mul_le_mul (coefficient_parameters_bound hD hδ hau.le hbu.le hcu.le n)
      (pow_le_pow_left₀ (norm_nonneg _) hxu.le n) (by positivity) (norm_nonneg _)
  have hs := (tendstoUniformlyOn_tsum hM hbound).continuousOn
    (Eventually.frequently (Eventually.of_forall (fun s => continuousOn_finsetSum s (fun n _ => hterms n))))
  have he : (fun u => ∑' n,ordinaryHypergeometricCoefficient (A u) (B u) (C u) n*(X u)^n)=
      (fun u => ordinaryHypergeometric (A u) (B u) (C u) (X u)) := by
    funext u
    simp only [ordinaryHypergeometric_eq_tsum,smul_eq_mul]
  rw [he] at hs
  exact hs.continuousAt (hUopen.mem_nhds hpU)

end
end jacobi.Reference.Hypergeometric
