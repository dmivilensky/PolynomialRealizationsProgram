import chebyshev2.SineContinuum.GreenFlux

/-!
Article: chebyshev2, Proposition 2.
The literal continuous Green kernel has every printed eigenfunction and its exact eigenvalue.
Use: `chebyshev2.SineContinuum.green_eigenfunction` feeds
`chebyshev2.SineContinuum.greenRow_eigenfunction` (green Row eigenfunction).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `IntervalIntegrable (fun t => l t*upsilon n t) volume 0 1`.

Use: `chebyshev2.SineContinuum.leftFlux_integral` uses this identity to establish exact
identity `mu n*(∫ s in (0:ℝ)..t, l s*upsilon n s)=leftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.l_continuousOn`,
`chebyshev2.SineContinuum.upsilon_continuous` with the arguments shown in the proof.
-/
theorem l_upsilon_integrable (n : ℕ) : IntervalIntegrable (fun t => l t*upsilon n t) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact l_continuousOn.mul (upsilon_continuous n).continuousOn

/--
The stated quantitative bound `IntervalIntegrable (fun t => r t*upsilon n t) volume 0 1`.

Use: `chebyshev2.SineContinuum.rightFlux_integral` uses this identity to establish exact
identity `mu n*(∫ s in t..(1:ℝ), r s*upsilon n s)=-rightFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.r_continuousOn`,
`chebyshev2.SineContinuum.upsilon_continuous` with the arguments shown in the proof.
-/
theorem r_upsilon_integrable (n : ℕ) : IntervalIntegrable (fun t => r t*upsilon n t) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact r_continuousOn.mul (upsilon_continuous n).continuousOn

/--
Exact identity `mu n*(∫ s in (0:ℝ)..t, l s*upsilon n s)=leftFlux n t`.

Use: `chebyshev2.SineContinuum.green_split_eigenfunction` uses this identity to establish
exact identity `(1/2)*(r t*(∫ s in (0:ℝ)..t, l s*upsilon n s)+ l t*(∫ s in t..(1:ℝ), r
s*upsilon n s))=upsilon n t/mu n`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem leftFlux_integral (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    mu n*(∫ s in (0:ℝ)..t, l s*upsilon n s)=leftFlux n t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hi : IntervalIntegrable (fun s => mu n*l s*upsilon n s) volume 0 t := by
    have hc := (l_upsilon_integrable n).mono_set (show uIcc (0:ℝ) t ⊆ uIcc (0:ℝ) 1 by
      rw [uIcc_of_le ht.1.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht.2.le)
    convert hc.const_mul (mu n) using 1
    funext s; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun s hs => leftFlux_derivative n ⟨hs.1,hs.2.trans ht.2⟩) hi (leftFlux_zero_limit n)
    ((leftFlux_derivative n ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have he : (fun s => mu n*l s*upsilon n s)=(fun s => mu n*(l s*upsilon n s)) := by funext s; ring
  rw [he,intervalIntegral.integral_const_mul,sub_zero] at h
  exact h

/--
Exact identity `mu n*(∫ s in t..(1:ℝ), r s*upsilon n s)=-rightFlux n t`.

Use: `chebyshev2.SineContinuum.green_split_eigenfunction` uses this identity to establish
exact identity `(1/2)*(r t*(∫ s in (0:ℝ)..t, l s*upsilon n s)+ l t*(∫ s in t..(1:ℝ), r
s*upsilon n s))=upsilon n t/mu n`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightFlux_integral (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    mu n*(∫ s in t..(1:ℝ), r s*upsilon n s)=-rightFlux n t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hi : IntervalIntegrable (fun s => mu n*r s*upsilon n s) volume t 1 := by
    have hc := (r_upsilon_integrable n).mono_set (show uIcc t (1:ℝ) ⊆ uIcc (0:ℝ) 1 by
      rw [uIcc_of_le ht.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_left ht.1.le)
    convert hc.const_mul (mu n) using 1
    funext s; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.2
    (fun s hs => rightFlux_derivative n ⟨ht.1.trans hs.1,hs.2⟩) hi
    ((rightFlux_derivative n ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (rightFlux_one_limit n)
  have he : (fun s => mu n*r s*upsilon n s)=(fun s => mu n*(r s*upsilon n s)) := by funext s; ring
  rw [he,intervalIntegral.integral_const_mul,zero_sub] at h
  exact h

/--
The split Green formula equals the exact spectral inverse on every sine--Legendre
eigenfunction. Both endpoint fluxes have been proved to vanish.

Exact identity `(1/2)*(r t*(∫ s in (0:ℝ)..t, l s*upsilon n s)+ l t*(∫ s in t..(1:ℝ), r
s*upsilon n s))=upsilon n t/mu n`.

Use: `chebyshev2.SineContinuum.green_eigenfunction` uses this identity to establish exact
identity `(∫ s in (0:ℝ)..1, green t s*upsilon n s)=upsilon n t/mu n`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.leftFlux_integral`,
`chebyshev2.SineContinuum.rightFlux_integral`,
`chebyshev2.SineContinuum.wronskian_eq_two` with the arguments shown in the proof.
-/
theorem green_split_eigenfunction (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (1/2)*(r t*(∫ s in (0:ℝ)..t, l s*upsilon n s)+
      l t*(∫ s in t..(1:ℝ), r s*upsilon n s))=upsilon n t/mu n := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.leftFlux_integral`,
  -- `chebyshev2.SineContinuum.rightFlux_integral`,
  -- `chebyshev2.SineContinuum.wronskian_eq_two` with the arguments shown in the proof.
  have hl := leftFlux_integral n ht
  have hr := rightFlux_integral n ht
  have hw := wronskian_eq_two ht
  dsimp [leftFlux,rightFlux,wronskian] at hl hr hw
  apply (eq_div_iff (mu_positive n).ne').mpr
  linear_combination (1/2)*r t*hl+(1/2)*l t*hr+(1/2)*upsilon n t*hw

/--
The literal continuous Green kernel has every printed eigenfunction and its exact eigenvalue.

Exact identity `(∫ s in (0:ℝ)..1, green t s*upsilon n s)=upsilon n t/mu n`.

Use: `chebyshev2.SineContinuum.greenRow_eigenfunction` uses this identity to establish
exact identity `inner ℝ (greenRow t) (sineHilbertBasis n)=upsilon n t/mu n`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.green_continuousOn`,
`chebyshev2.SineContinuum.upsilon_continuous`,
`chebyshev2.SineContinuum.green_split_eigenfunction` with the arguments shown in the proof.
-/
theorem green_eigenfunction (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, green t s*upsilon n s)=upsilon n t/mu n := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.green_continuousOn`,
  -- `chebyshev2.SineContinuum.upsilon_continuous`,
  -- `chebyshev2.SineContinuum.green_split_eigenfunction` with the arguments shown in the
  -- proof.
  have h₁ : IntervalIntegrable (fun s => green t s*upsilon n s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1.le]
    apply (green_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨ht.1.le,ht.2.le⟩,⟨hs.1,hs.2.trans ht.2.le⟩⟩)).mul
      (upsilon_continuous n).continuousOn
  have h₂ : IntervalIntegrable (fun s => green t s*upsilon n s) volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.2.le]
    apply (green_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨ht.1.le,ht.2.le⟩,⟨ht.1.le.trans hs.1,hs.2⟩⟩)).mul
      (upsilon_continuous n).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
  have hl : (∫ s in (0:ℝ)..t, green t s*upsilon n s)=
      (1/2)*r t*(∫ s in (0:ℝ)..t, l s*upsilon n s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1.le] at hs
    dsimp [green]
    rw [min_eq_right hs.2,max_eq_left hs.2]
    ring
  have hr : (∫ s in t..(1:ℝ), green t s*upsilon n s)=
      (1/2)*l t*(∫ s in t..(1:ℝ), r s*upsilon n s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.2.le] at hs
    dsimp [green]
    rw [min_eq_left hs.1,max_eq_right hs.1]
    ring
  rw [hl,hr]
  convert green_split_eigenfunction n ht using 1; ring

end
end chebyshev2.SineContinuum
