import jacobi.Bessel.OrdinaryPhase
import jacobi.Oscillation.PhaseMeanValue

/-!
Article: jacobi, Proposition B.1.
The genuine ordinary phase is compared with the identity between an
actual original Bessel zero and the true nearby finite argument. The
proved original finite-root error gains an integrable inverse-square
factor, giving a uniform inverse-square frequency error after conversion.
Use: converts the original averaged finite/Bessel phase identity into the sharp source angular estimate, without assuming the classical J/Y phase derivative estimates.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set jacobi.Oscillation
set_option backward.isDefEq.respectTransparency false

/-- A nearby actual argument has its genuine Bessel phase displacement equal to its actual zero displacement up to an explicit uniform inverse-square frequency error.
Use: converts the original averaged finite/Bessel phase identity into the sharp source angular estimate, without assuming the classical J/Y phase derivative estimates.
Article: jacobi, Proposition B.1.
Proof: every point of the original joining interval is at least j_k/2.
The true Bessel phase derivative minus one is bounded by 4*|c_0|/j_k^2.
The proved finite-root displacement supplies the remaining j_k/N^2;
monotonicity of the original numbered zeros bounds its last reciprocal
by the fixed actual base zero reciprocal. -/
theorem ordinaryPhase_zero_displacement {a X N Q : ℝ} (ha : -1<a) {k0 k : ℕ}
    (hN : 0<N) (hQ : 0≤Q) (hk : k0≤k)
    (hX : positiveZero a ha k/2≤X)
    (herror : |X-positiveZero a ha k|≤Q*positiveZero a ha k/N^2) :
    |(ordinaryPhase a ha (positiveZero a ha k0) X-
      ordinaryPhase a ha (positiveZero a ha k0) (positiveZero a ha k))-(X-positiveZero a ha k)|≤
        (4*|1/4-a^2| *Q/positiveZero a ha k0)/N^2 := by
  -- The entire estimate is for the original state-integral phase and the same true exhaustive Bessel zero sequence.
  let j := positiveZero a ha k
  let s := positiveZero a ha k0
  let g := ordinaryPhase a ha s
  have hj : 0<j := (positiveZero_properties ha k).1
  have hs : 0<s := (positiveZero_properties ha k0).1
  have hjs : s≤j := (positiveZero_strictMono ha).monotone hk
  have hbox : ∀ x∈uIcc j X,j/2≤x := fun x hx =>
    le_trans (le_min (by linarith) hX) hx.1
  have h := phase_identity_remainder (f := g) (e := fun _ => 0) (epsilon := 0)
    (c := 1/4-a^2) (show 0<j/2 by positivity) hbox
    (fun x hx => by
      have hxp : 0<x := lt_of_lt_of_le (by positivity : 0<j/2) (hbox x hx)
      simpa only [add_zero] using ordinaryPhase_hasDerivAt ha hs hxp (wave_positiveZero_zero ha k0))
    (fun _ _ => by norm_num)
  simp only [add_zero] at h
  have hmult := mul_le_mul_of_nonneg_left herror (show 0≤ |1/4-a^2|/(j/2)^2 by positivity)
  have he : (|1/4-a^2|/(j/2)^2)*(Q*j/N^2)=(4*|1/4-a^2| *Q/j)/N^2 := by
    field_simp [hj.ne',hN.ne']
    ring
  calc
    _ ≤ (|1/4-a^2|/(j/2)^2)*|X-j| := h
    _ ≤ (|1/4-a^2|/(j/2)^2)*(Q*j/N^2) := hmult
    _ = (4*|1/4-a^2| *Q/j)/N^2 := he
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) hs hjs) (sq_nonneg N)

end
end jacobi.Bessel
