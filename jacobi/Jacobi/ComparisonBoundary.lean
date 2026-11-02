import jacobi.Jacobi.EndpointFactor
import jacobi.Jacobi.Angles
import jacobi.Bessel.ScaledWave
import jacobi.Bessel.SturmZeros

/-!
Article: jacobi, Proposition B.1.
The actual Jacobi and scaled Bessel waves satisfy the genuine zero endpoint
Wronskian condition and both select the positive initial branch. Every
angular zero and the symmetric middle zero are identified with the original
canonical finite Jacobi zero enumeration.
Use: discharges the singular Sturm boundary hypothesis for the actual source functions throughout alpha,beta>-1.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Jacobi and positive-frequency Bessel waves have a genuine zero Wronskian limit at the singular endpoint.
Use: discharges the singular Sturm boundary hypothesis for the actual source functions throughout alpha,beta>-1.
Article: jacobi, Proposition B.1.
Proof: both original waves have proved common power theta^(alpha+1/2)
and actual even analytic endpoint factors with zero first derivatives.
The established power-factor theorem identifies their original slopes and
proves the endpoint limit with positive residual exponent 2*alpha+2. -/
theorem comparison_wronskian_zero {a b D : ℝ} (ha : -1<a) (hD : 0<D) (n : ℕ) :
    Tendsto (fun x : ℝ => liouvilleSlope a b n x* jacobi.Bessel.scaledWave a D x-
      liouville a b n x* jacobi.Bessel.scaledWaveSlope a D x) (𝓝[>] 0) (𝓝 0) := by
  -- Every endpoint factor and every original derivative in this application was proved independently for the actual source functions.
  apply jacobi.Bessel.wronskian_tendsto_of_endpoint_factors (p := a+1/2) (e := Real.pi)
    (g := endpointFactor a b n) (h := jacobi.Bessel.scaledEndpointFactor a D)
    (by linarith) Real.pi_pos (endpointFactor_analytic a b n)
    (jacobi.Bessel.scaledEndpointFactor_properties a D 0).1
    (endpointFactor_properties a b n).2 (jacobi.Bessel.scaledEndpointFactor_zero ha D).2
    (fun x hx => liouville_hasDerivAt a b n hx)
    (fun x hx => jacobi.Bessel.scaledWave_hasDerivAt a hD hx.1)
  · intro x hx
    exact liouville_endpoint_factor a b n hx
  · intro x hx
    exact jacobi.Bessel.scaledWave_endpoint_factor a hD hx.1

/-- The actual Jacobi Liouville wave is strictly positive near its selected singular endpoint.
Use: fixes the original branch sign in the first-interval comparison of numbered zeros.
Article: jacobi, Proposition B.1.
Proof: the actual analytic regular factor has a strictly positive central
value. Continuity preserves this sign, and its actual positive-power
factorization preserves positivity on the positive angle branch. -/
theorem liouville_positive_near_zero (a b : ℝ) (n : ℕ) :
    ∀ᶠ x in 𝓝[>] (0:ℝ),0<liouville a b n x := by
  have hp := (endpointFactor_analytic a b n).continuousAt.eventually
    (Ioi_mem_nhds (endpointFactor_properties a b n).1)
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos,hp.filter_mono nhdsWithin_le_nhds] with x hx hpx
  rw [liouville_endpoint_factor a b n hx]
  exact mul_pos (Real.rpow_pos_of_pos hx.1 _) hpx

/-- Every actual canonical Jacobi zero angle is a zero of the original Liouville wave.
Use: the Sturm intervals end at actual source zeros, rather than an assumed angular list.
Article: jacobi, Proposition B.1.
Proof: the positive wave weight preserves zeros, and the true inverse-cosine angle evaluates to the actual zero of the original polynomial. -/
theorem liouville_angle_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    liouville a b n (angle a b ha hb i)=0 := by
  rw [liouville_zero_iff a b n (angle_properties ha hb i).1,(angle_properties ha hb i).2]
  exact (realNormalized_zero_iff _ _ _ _).mpr (nodes_are_zeros ha hb i)

/-- Every actual Liouville zero in the physical angle interval has exactly one index in the genuine finite Jacobi angle list.
Use: supplies the complete nodal intervals and minimality needed in the numbered Sturm comparison.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: remove the actual positive weight and use completeness of the
original shifted polynomial roots. The principal inverse-cosine branch
recovers exactly the original angle. -/
theorem liouville_zero_exhaustive {a b x : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (hx : x∈Ioo 0 Real.pi) (hz : liouville a b n x=0) :
    ∃ i : Fin n,angle a b ha hb i=x := by
  -- Both the zero and its canonical index belong to the original finite polynomial.
  have hangular : angular a b n x=0 :=
    (mul_eq_zero.mp hz).resolve_left (liouvilleWeight_pos a b hx).ne'
  obtain ⟨i,hi⟩ := (shiftedRoots_exhaustive ha hb n _).mp hangular
  refine ⟨i,?_⟩
  change arccos (1-2*shiftedRoots a b ha hb n i)=x
  rw [hi]
  convert Real.arccos_cos hx.1.le hx.2.le using 1
  congr 1
  ring

/-- The actual Jacobi oscillation frequency is strictly positive at every positive source degree in the full parameter range.
Use: justifies its real square-root and positive-frequency Bessel comparisons without a large-degree branch premise.
Article: jacobi, Proposition B.1.
Proof: n>=1 and alpha,beta>-1 give N>1/2. -/
theorem frequency_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    0<frequency a b n := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  dsimp [frequency]
  linarith

/-- The actual symmetric Jacobi polynomial of odd degree has its canonical middle node exactly zero.
Use: anchors the genuine numbered Bessel phase by comparison with a known source zero, avoiding an imported Bessel phase formula.
Article: jacobi, Proposition B.1.
Proof: the middle finite index is fixed by reversal; ordered parameter
reflection makes that same original node equal to its own negative. -/
theorem symmetric_middle_node {a : ℝ} (ha : -1<a) (k : ℕ) :
    (nodes a a ha ha (2*k+1)).value ⟨k,by omega⟩=0 := by
  have hr : (⟨k,by omega⟩ : Fin (2*k+1)).rev=⟨k,by omega⟩ := by
    apply Fin.ext
    simp only [Fin.rev]
    omega
  have h := nodes_reflection ha ha (⟨k,by omega⟩ : Fin (2*k+1))
  rw [hr] at h
  linarith

/-- The actual symmetric odd-degree Jacobi middle zero angle is exactly pi/2.
Use: fixes the leading numbered Bessel phase through genuine Sturm bounds at a known canonical finite zero.
Article: jacobi, Proposition B.1.
Proof: the original middle node is zero and the true principal inverse cosine of zero is pi/2. -/
theorem symmetric_middle_angle {a : ℝ} (ha : -1<a) (k : ℕ) :
    angle a a ha ha (⟨k,by omega⟩ : Fin (2*k+1))=Real.pi/2 := by
  rw [angle,symmetric_middle_node ha k,Real.arccos_zero]

end
end jacobi.Jacobi
