import jacobi.Jacobi.ComparisonZeros
import jacobi.Bessel.ScaledZeros

/-!
Article: jacobi, Proposition B.1.
Both directions of strict frequency comparison are proved for the original
Jacobi and Bessel functions and their complete actual zero lists. All
singular boundary and zero-numbering conditions are discharged by their
previously proved source identities, leaving only the literal potential order.
Use: the genuine compact remainder bound gives the upper McMahon phase bound and uniform first-order angular comparison.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set jacobi.Bessel
set_option backward.isDefEq.respectTransparency false

/-- An actual higher-frequency Bessel zero precedes the same canonically numbered original Jacobi angle whenever the true regular potentials are strictly ordered.
Use: the genuine compact remainder bound gives the upper McMahon phase bound and uniform first-order angular comparison.
Article: jacobi, Proposition B.1.
Proof: instantiate the shared numbered Sturm theorem with the actual
Jacobi and scaled Bessel waves. Their original derivatives, equations,
singular Wronskian, initial positive branches, complete nodal intervals,
and actual first/successor minimality have all already been proved. -/
theorem bessel_zero_lt_angle {a b D R : ℝ} (ha : -1<a) (hb : -1<b) (hD : 0<D)
    (hR : R<Real.pi) {n K : ℕ} (hK : K<n)
    (hAngle : finiteAngleAt a b ha hb n K≤R)
    (hpot : ∀ x∈Ioo 0 R,(frequency a b n)^2+regularPotential a b x<D^2) :
    ∀ k≤K,scaledZero a ha D k<finiteAngleAt a b ha hb n k := by
  -- The only remaining comparison premise is the literal scalar potential order; no phase or zero convergence is assumed.
  have hn : 0<n := by omega
  have hphys : ∀ x∈Ioc 0 R,x∈Ioo 0 Real.pi := fun x hx => ⟨hx.1,hx.2.trans_lt hR⟩
  apply numbered_sturm_comparison (R := R) K (finiteAngleAt a b ha hb n) (scaledZero a ha D)
    (f := liouville a b n) (f' := liouvilleSlope a b n) (f'' := liouvilleAcceleration a b n)
    (g := scaledWave a D) (g' := scaledWaveSlope a D) (g'' := scaledWaveAcceleration a D)
    (q0 := fun x => (frequency a b n)^2+endpointCorrection a/x^2+regularPotential a b x)
    (q1 := fun x => D^2+endpointCorrection a/x^2)
    (fun x hx => liouville_hasDerivAt a b n (hphys x hx))
    (fun x hx => liouvilleSlope_hasDerivAt a b n (hphys x hx))
    (fun x hx => scaledWave_hasDerivAt a hD hx.1)
    (fun x hx => scaledWaveSlope_hasDerivAt a hD hx.1)
    (fun x hx => liouville_regular_equation ha n (hphys x ⟨hx.1,hx.2.le⟩))
    (fun x hx => scaledWave_equation ha hD hx.1)
    (fun x hx => by linarith [hpot x hx])
    (comparison_wronskian_zero ha hD n) (liouville_positive_near_zero a b n)
    (scaledWave_positive_near_zero ha hD)
  · intro m hm
    have hmN : m<n := hm.trans_lt hK
    refine ⟨(finiteAngleAt_interval ha hb hmN).1,?_⟩
    by_cases hmK : m=K
    · simpa only [hmK] using hAngle
    · exact (finiteAngleAt_lt ha hb (lt_of_le_of_ne hm hmK) hK).le.trans hAngle
  · intro m hm
    exact finiteAngleAt_lt ha hb (Nat.lt_succ_self m) ((show m+1≤K by omega).trans_lt hK)
  · intro m hm
    exact finiteAngleAt_is_zero ha hb (hm.trans_lt hK)
  · exact fun x hx => finiteAngleAt_no_zero_before ha hb hn hx
  · intro m hm x hx
    exact finiteAngleAt_no_zero_between ha hb ((show m+1≤K by omega).trans_lt hK) hx
  · exact fun x hx hz => scaledZero_first_le ha hD hx.1 hz
  · exact fun m _ x hx hz hlt => scaledZero_successor_le ha hD hx.1 hz m hlt

/-- An actual lower-frequency Bessel zero follows the same numbered original Jacobi angle whenever its coefficient is strictly below the true Jacobi potential.
Use: provides the reverse bound needed for the exact indexed Bessel phase and uniform Jacobi zero comparison.
Article: jacobi, Proposition B.1.
Proof: exchange the actual two original equations in the same numbered
Sturm theorem. The true endpoint Wronskian changes sign and still tends
to zero. The complete genuine Jacobi zero list supplies the comparator
minimality, and the genuine Bessel list supplies all original nodal intervals. -/
theorem angle_lt_bessel_zero {a b D R : ℝ} (ha : -1<a) (hb : -1<b) (hD : 0<D)
    (hR : R<Real.pi) {n K : ℕ} (hK : K<n)
    (hZero : scaledZero a ha D K≤R)
    (hpot : ∀ x∈Ioo 0 R,D^2<(frequency a b n)^2+regularPotential a b x) :
    ∀ k≤K,finiteAngleAt a b ha hb n k<scaledZero a ha D k := by
  -- The same actual functions are used in reverse order, including their independently established singular endpoint branch.
  have hn : 0<n := by omega
  have hphys : ∀ x∈Ioc 0 R,x∈Ioo 0 Real.pi := fun x hx => ⟨hx.1,hx.2.trans_lt hR⟩
  apply numbered_sturm_comparison (R := R) K (scaledZero a ha D) (finiteAngleAt a b ha hb n)
    (f := scaledWave a D) (f' := scaledWaveSlope a D) (f'' := scaledWaveAcceleration a D)
    (g := liouville a b n) (g' := liouvilleSlope a b n) (g'' := liouvilleAcceleration a b n)
    (q0 := fun x => D^2+endpointCorrection a/x^2)
    (q1 := fun x => (frequency a b n)^2+endpointCorrection a/x^2+regularPotential a b x)
    (fun x hx => scaledWave_hasDerivAt a hD hx.1)
    (fun x hx => scaledWaveSlope_hasDerivAt a hD hx.1)
    (fun x hx => liouville_hasDerivAt a b n (hphys x hx))
    (fun x hx => liouvilleSlope_hasDerivAt a b n (hphys x hx))
    (fun x hx => scaledWave_equation ha hD hx.1)
    (fun x hx => liouville_regular_equation ha n (hphys x ⟨hx.1,hx.2.le⟩))
    (fun x hx => by linarith [hpot x hx])
    (by simpa only [neg_zero,neg_sub,mul_comm] using (comparison_wronskian_zero ha hD n).neg)
    (scaledWave_positive_near_zero ha hD) (liouville_positive_near_zero a b n)
  · intro m hm
    exact ⟨scaledZero_pos ha hD m,((scaledZero_strictMono ha hD).monotone hm).trans hZero⟩
  · exact fun m _ => scaledZero_strictMono ha hD (Nat.lt_succ_self m)
  · exact fun m _ => scaledZero_is_zero ha hD m
  · exact fun x hx => scaledWave_no_zero_before ha hD hx
  · exact fun m _ x hx => scaledWave_no_zero_between ha hD m hx
  · exact fun x hx hz => finiteAngleAt_first_le ha hb hn (hphys x hx) hz
  · intro m hm x hx hz hlt
    exact finiteAngleAt_successor_le ha hb ((show m+1≤K by omega).trans_lt hK) (hphys x hx) hz hlt

end
end jacobi.Jacobi
