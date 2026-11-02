import jacobi.Bessel.OrdinaryPhase
import jacobi.Oscillation.PhaseInvariantVariation

/-!
Article: jacobi, Proposition B.1.
The exact corrected phase is evaluated along the genuine numbered Bessel
zeros. Its limit is fixed by the proved indexed Weyl phase, so finite
variation gives an unconditional cubic zero correction. All functions
and zero indices in this argument are the original source functions.
Use: evaluates the modified phase at large genuine Bessel zeros while retaining the exact base index.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The precise leading phase adds exactly one pi per actual index step.
Use: evaluates the modified phase at large genuine Bessel zeros while retaining the exact base index.
Article: jacobi, Proposition B.1.
Proof: substitute the explicit affine phase grid and the natural-index sum. -/
theorem phaseGrid_add (a : ℝ) (k m : ℕ) :
    phaseGrid a (k+m)=phaseGrid a k+(m:ℝ)*Real.pi := by
  unfold phaseGrid
  push_cast
  ring

/-- At the genuine numbered zeros the corrected actual phase converges to the negative leading phase of its original base zero.
Use: identifies the limiting value needed in the cubic variation estimate, without assuming any classical asymptotic phase formula.
Article: jacobi, Proposition B.1.
Proof: exact phase increments replace each terminal phase by m*pi. The
proved indexed Weyl error tends to zero, and the actual positive zeros
tend to infinity, so both reciprocal correction terms vanish. -/
theorem phaseInvariant_numbered_tendsto {a : ℝ} (ha : -1<a) (k : ℕ)
    (hk : 2*(a^2+1)≤positiveZero a ha k) :
    Tendsto (fun m : ℕ => phaseInvariant (1/4-a^2) (ordinaryPhase a ha (positiveZero a ha k))
      (positiveZero a ha (k+m))) atTop (𝓝 (-phaseGrid a k)) := by
  -- The terminal sequence consists of every later original numbered zero, so its limiting constant has no undetermined multiple of pi.
  have hind : Tendsto (fun m : ℕ => k+m) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
  have herr := (positiveZero_phase_tendsto ha).comp hind
  have hi := tendsto_inv_atTop_zero.comp ((positiveZero_tendsto ha).comp hind)
  have hmain : Tendsto (fun m : ℕ => (m:ℝ)*Real.pi-positiveZero a ha (k+m))
      atTop (𝓝 (-phaseGrid a k)) := by
    have h := herr.neg.sub_const (phaseGrid a k)
    simp only [neg_zero,zero_sub] at h
    convert h using 1
    ext m
    simp only [Function.comp_def,phaseGrid_add]
    ring
  have h1 : Tendsto (fun m : ℕ => (1/4-a^2)/(2*positiveZero a ha (k+m))) atTop (𝓝 0) := by
    convert hi.const_mul ((1/4-a^2)/2) using 1
    · ext m; simp only [Function.comp_def,div_eq_mul_inv,mul_inv_rev]; ring
    · norm_num
  have h3 : Tendsto (fun m : ℕ => (1/4-a^2)/(4*(positiveZero a ha (k+m))^3)) atTop (𝓝 0) := by
    convert (hi.pow 3).const_mul ((1/4-a^2)/4) using 1
    · ext m; simp only [Function.comp_def,div_eq_mul_inv,mul_inv_rev,inv_pow]; ring
    · norm_num
  have h := (hmain.add h1).sub h3
  simp only [add_zero,sub_zero] at h
  convert h using 1
  ext m
  rw [phaseInvariant_at_zero (by rw [ordinaryPhase_numbered_zero ha k hk m]; exact Real.sin_nat_mul_pi m),
    ordinaryPhase_numbered_zero ha k hk m]

/-- Beyond the explicit restoring threshold, each original Bessel zero has a reciprocal-zero correction with a uniform cubic remainder.
Use: replacement of the genuine reciprocal zero by its leading phase gives exactly McMahon's printed cubic error B2.
Article: jacobi, Proposition B.1.
Proof: integrate the exact modified phase between the original base zero
and each later numbered zero. Its genuine terminal limit is the negative
indexed leading phase. Pass the finite cubic variation bound to that
limit, evaluate the actual base phase zero, and bound its remaining cubic
term by the triangle inequality. -/
theorem positiveZero_reciprocal_cubic {a : ℝ} (ha : -1<a) (k : ℕ)
    (hk : 2*(a^2+1)≤positiveZero a ha k) :
    |positiveZero a ha k-phaseGrid a k-(1/4-a^2)/(2*positiveZero a ha k)|≤
      (((1/4-a^2)^2+|1/4-a^2|)/3+|1/4-a^2|/4)/(positiveZero a ha k)^3 := by
  -- The bound is obtained for the original wave and its actual zero enumeration; there is no phase or asymptotic input certificate.
  let c : ℝ := 1/4-a^2
  let x := positiveZero a ha k
  let theta := ordinaryPhase a ha x
  have hx : 1≤x := by dsimp [x]; nlinarith [sq_nonneg a]
  have hxp : 0<x := (positiveZero_properties ha k).1
  have hlim := phaseInvariant_numbered_tendsto ha k hk
  have hb : ∀ m : ℕ,|phaseInvariant c theta (positiveZero a ha (k+m))-phaseInvariant c theta x|
      ≤(c^2+|c|)/(3*x^3) := by
    intro m
    apply phaseInvariant_variation hx ((positiveZero_strictMono ha).monotone (Nat.le_add_right k m))
    intro t ht
    exact ordinaryPhase_hasDerivAt ha hxp (hxp.trans_le ht.1) (wave_positiveZero_zero ha k)
  have hpass := le_of_tendsto ((hlim.sub_const (phaseInvariant c theta x)).abs) (Filter.Eventually.of_forall hb)
  have hzero : theta x=0 := (restoringState a ha).phase_self x
  have he : phaseInvariant c theta x= -x+c/(2*x)-c/(4*x^3) := by
    rw [phaseInvariant_at_zero (by rw [hzero,Real.sin_zero]),hzero,zero_sub]
  rw [he] at hpass
  have hid : x-phaseGrid a k-c/(2*x)=
      (-phaseGrid a k-(-x+c/(2*x)-c/(4*x^3)))-c/(4*x^3) := by ring
  change |x-phaseGrid a k-c/(2*x)|≤((c^2+|c|)/3+|c|/4)/x^3
  rw [hid]
  calc
    _ ≤ |-phaseGrid a k-(-x+c/(2*x)-c/(4*x^3))|+|c/(4*x^3)| := abs_sub _ _
    _ ≤ (c^2+|c|)/(3*x^3)+|c|/(4*x^3) := by
      rw [abs_div,abs_of_pos (by positivity : 0<4*x^3)]
      exact add_le_add hpass le_rfl
    _ = _ := by ring

end
end jacobi.Bessel
