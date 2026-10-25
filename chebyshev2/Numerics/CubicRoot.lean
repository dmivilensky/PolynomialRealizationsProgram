import chebyshev2.Calibration.CubicRoot
import chebyshev2.Calculus.CubicSides
import LeanCert.Core.IntervalRat.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: chebyshev2, Section 4.1.
Lemma 19: the actual positive root, monotonicity, elementary bounds and exact rational bracketing.
Use: `chebyshev2.Numerics.cubicBracketCheck_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.cubicCheck_sound` (cubic Check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real LeanCert.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Defines `positiveCubic` of type `ℝ` by `chebyshev2.Calibration.positiveRoot 1 (a/3) b`.

Use: `chebyshev2.Numerics.positiveCubic_bounds` uses this definition to establish the
stated quantitative bound `max (sqrt a) (chebyshev2.Calculus.cubeRoot b)≤positiveCubic a b
∧ positiveCubic a b≤sqrt a+chebyshev2.Calculus.cubeRoot b`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def positiveCubic (a b : ℝ) : ℝ := chebyshev2.Calibration.positiveRoot 1 (a/3) b

 /--
Exact identity `0<positiveCubic a b ∧ (positiveCubic a b)^3-a*positiveCubic a b-b=0`.

Use: `chebyshev2.Numerics.positiveCubic_bounds` uses this identity to establish the stated
quantitative bound `max (sqrt a) (chebyshev2.Calculus.cubeRoot b)≤positiveCubic a b ∧
positiveCubic a b≤sqrt a+chebyshev2.Calculus.cubeRoot b`.

Article: chebyshev2, Lemma 19.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_spec` with the
arguments shown in the proof.
-/
theorem positiveCubic_spec {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    0<positiveCubic a b ∧ (positiveCubic a b)^3-a*positiveCubic a b-b=0 := by
  obtain ⟨hp,he⟩ := chebyshev2.Calibration.positiveRoot_spec (Q := a/3) (by norm_num : (0:ℝ)<1) (div_nonneg ha (by norm_num)) hb
  refine ⟨hp,?_⟩
  dsimp only [chebyshev2.Calibration.cubic] at he
  dsimp only [positiveCubic]
  nlinarith [he]

 /--
Membership in the specified domain/enclosure: `positiveCubic a b∈Icc l u`.

Use: `chebyshev2.Numerics.cubicBracketCheck_sound` uses this assertion to establish
membership in the specified domain/enclosure: `positiveCubic a b∈X`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.cubic_neg_iff`,
`chebyshev2.Calibration.cubic_pos_iff` with the arguments shown in the proof.
-/
theorem positiveCubic_bracket {a b l u : ℝ} (ha : 0≤a) (hb : 0<b)
    (hl : 0≤l) (hu : 0≤u) (hlo : l^3-a*l-b≤0) (hup : 0≤u^3-a*u-b) :
    positiveCubic a b∈Icc l u := by
  -- Use the identities/estimates `chebyshev2.Calibration.cubic_neg_iff`,
  -- `chebyshev2.Calibration.cubic_pos_iff` with the arguments shown in the proof.
  have hn := chebyshev2.Calibration.cubic_neg_iff (Q := a/3) (by norm_num : (0:ℝ)<1) (div_nonneg ha (by norm_num)) hb hu
  have hp := chebyshev2.Calibration.cubic_pos_iff (Q := a/3) (by norm_num : (0:ℝ)<1) (div_nonneg ha (by norm_num)) hb hl
  constructor
  · apply le_of_not_gt
    intro h
    have hh := hp.mpr h
    dsimp only [chebyshev2.Calibration.cubic] at hh
    nlinarith
  · apply le_of_not_gt
    intro h
    have hh := hn.mpr h
    dsimp only [chebyshev2.Calibration.cubic] at hh
    nlinarith

 /--
The stated quantitative bound `positiveCubic a b≤positiveCubic a' b'`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 19.

Proof: Use the identities/estimates `chebyshev2.Numerics.positiveCubic_spec`,
`chebyshev2.Numerics.positiveCubic_bracket` with the arguments shown in the proof.
-/
theorem positiveCubic_mono {a b a' b' : ℝ} (ha : 0≤a) (hb : 0<b)
    (haa : a≤a') (hbb : b≤b') : positiveCubic a b≤positiveCubic a' b' := by
  obtain ⟨hz,he⟩ := positiveCubic_spec (ha.trans haa) (hb.trans_le hbb)
  exact (positiveCubic_bracket ha hb (by positivity : (0:ℝ)≤0) hz.le (by simpa using hb.le)
    (by nlinarith [mul_le_mul_of_nonneg_right haa hz.le])).2

 /--
Exact identity `positiveCubic a b=z`.

Use: `chebyshev2.Numerics.ReferenceJetSource.root_value` uses this identity to establish
exact identity `(root R W).value t=(referenceData R).normalizedRoot t`.

Article: chebyshev2, Lemma 19.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_eq` with the
arguments shown in the proof.
-/
theorem positiveCubic_unique {a b z : ℝ} (ha : 0≤a) (hb : 0<b)
    (hz : 0<z) (he : z^3-a*z-b=0) : positiveCubic a b=z := by
  apply chebyshev2.Calibration.positiveRoot_eq (Q := a/3) (by norm_num)
    (div_nonneg ha (by norm_num)) hb hz
  dsimp only [chebyshev2.Calibration.cubic]
  nlinarith

 /--
The stated quantitative bound `positiveCubic a b<positiveCubic a' b'`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 19.

Proof: Use the identities/estimates `chebyshev2.Numerics.positiveCubic_spec`,
`chebyshev2.Calibration.cubic_pos_iff` with the arguments shown in the proof.
-/
theorem positiveCubic_strict_mono {a b a' b' : ℝ} (ha : 0≤a) (hb : 0<b)
    (haa : a≤a') (hbb : b≤b') (hs : a<a' ∨ b<b') :
    positiveCubic a b<positiveCubic a' b' := by
  -- Use the identities/estimates `chebyshev2.Numerics.positiveCubic_spec`,
  -- `chebyshev2.Calibration.cubic_pos_iff` with the arguments shown in the proof.
  obtain ⟨hz,he⟩ := positiveCubic_spec (ha.trans haa) (hb.trans_le hbb)
  apply (chebyshev2.Calibration.cubic_pos_iff (Q := a/3) (by norm_num : (0:ℝ)<1)
    (div_nonneg ha (by norm_num)) hb hz.le).mp
  dsimp only [chebyshev2.Calibration.cubic]
  rcases hs with hs | hs
  · nlinarith [mul_lt_mul_of_pos_right hs hz]
  · nlinarith [mul_le_mul_of_nonneg_right haa hz.le]

/--
Mean-value witness for the interval Newton enclosure, including m=z.

Constructs witnesses with the exact properties `∃ ξ∈Icc l u,positiveCubic a
b=m-(m^3-a*m-b)/(3*ξ^2-a)`.

Use: `chebyshev2.Numerics.cubicNewton_sound` uses this identity to establish membership in
the specified domain/enclosure: `positiveCubic a b∈J`.

Article: chebyshev2, Lemma 19.

Proof: Use the identities/estimates `chebyshev2.Numerics.positiveCubic_spec` with the
arguments shown in the proof.
-/
theorem positiveCubic_newton {a b l u m : ℝ} (ha : 0≤a) (hb : 0<b)
    (hz : positiveCubic a b∈Icc l u) (hm : m∈Icc l u)
    (hd : ∀ x∈Icc l u,0<3*x^2-a) :
    ∃ ξ∈Icc l u,positiveCubic a b=m-(m^3-a*m-b)/(3*ξ^2-a) := by
  -- Use the identities/estimates `chebyshev2.Numerics.positiveCubic_spec` with the
  -- arguments shown in the proof.
  let z := positiveCubic a b
  let f := fun x : ℝ => x^3-a*x-b
  have he : f z=0 := (positiveCubic_spec ha hb).2
  -- Establish continuity hf before using the function at limits or in calculus arguments.
  have hf : Continuous f := by fun_prop
  have hder : ∀ x : ℝ,HasDerivAt f (3*x^2-a) x := by
    intro x
    convert (((hasDerivAt_id x).pow 3).sub ((hasDerivAt_id x).const_mul a)).sub_const b using 1 <;> simp [f,id_eq]
  rcases lt_trichotomy z m with h | h | h
  · obtain ⟨ξ,hξ,hξd⟩ := exists_hasDerivAt_eq_slope f (fun x => 3*x^2-a) h
      hf.continuousOn (fun x _ => hder x)
    have hmem : ξ∈Icc l u := ⟨hz.1.trans hξ.1.le,hξ.2.le.trans hm.2⟩
    refine ⟨ξ,hmem,?_⟩
    have hdne := ne_of_gt (hd ξ hmem)
    rw [he,sub_zero] at hξd
    have hprod := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp hξd
    have hr : (m^3-a*m-b)/(3*ξ^2-a)=m-z := by
      apply (div_eq_iff hdne).mpr
      dsimp only [f] at hprod
      nlinarith
    change z=m-(m^3-a*m-b)/(3*ξ^2-a)
    rw [hr]
    ring
  · refine ⟨m,hm,?_⟩
    change z=m-f m/(3*m^2-a)
    rw [← h,he,zero_div,sub_zero]
  · obtain ⟨ξ,hξ,hξd⟩ := exists_hasDerivAt_eq_slope f (fun x => 3*x^2-a) h
      hf.continuousOn (fun x _ => hder x)
    have hmem : ξ∈Icc l u := ⟨hm.1.trans hξ.1.le,hξ.2.le.trans hz.2⟩
    refine ⟨ξ,hmem,?_⟩
    have hdne := ne_of_gt (hd ξ hmem)
    rw [he,zero_sub] at hξd
    have hprod := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp hξd
    have hr : (m^3-a*m-b)/(3*ξ^2-a)=m-z := by
      apply (div_eq_iff hdne).mpr
      dsimp only [f] at hprod
      nlinarith
    change z=m-(m^3-a*m-b)/(3*ξ^2-a)
    rw [hr]
    ring

 /--
The stated quantitative bound `max (sqrt a) (chebyshev2.Calculus.cubeRoot b)≤positiveCubic
a b ∧ positiveCubic a b≤sqrt a+chebyshev2.Calculus.cubeRoot b`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 19.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem positiveCubic_bounds {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    max (sqrt a) (chebyshev2.Calculus.cubeRoot b)≤positiveCubic a b ∧
      positiveCubic a b≤sqrt a+chebyshev2.Calculus.cubeRoot b := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let z := positiveCubic a b
  obtain ⟨hz,he⟩ := positiveCubic_spec ha hb
  have hc := chebyshev2.Calculus.cubeRoot_cube hb.le
  have hcp := chebyshev2.Calculus.cubeRoot_pos hb
  have hs := sq_sqrt ha
  have hsp := sqrt_nonneg a
  have hlower : sqrt a≤z := by
    by_contra h
    have hsq : z^2<a := by nlinarith
    have hm := mul_lt_mul_of_pos_right hsq hz
    nlinarith
  have hcub : chebyshev2.Calculus.cubeRoot b≤z := by
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) hz.le
    rw [hc]
    nlinarith [mul_nonneg ha hz.le]
  refine ⟨max_le hlower hcub,?_⟩
  have hup : 0≤(sqrt a+chebyshev2.Calculus.cubeRoot b)^3-a*(sqrt a+chebyshev2.Calculus.cubeRoot b)-b := by
    calc
      0≤2*(sqrt a)^2*chebyshev2.Calculus.cubeRoot b+3*sqrt a*(chebyshev2.Calculus.cubeRoot b)^2 := by positivity
      _=(sqrt a+chebyshev2.Calculus.cubeRoot b)^3-a*(sqrt a+chebyshev2.Calculus.cubeRoot b)-b := by
        linear_combination -(sqrt a+chebyshev2.Calculus.cubeRoot b)*hs-hc
  exact (positiveCubic_bracket ha hb (by positivity : (0:ℝ)≤0) (by positivity)
    (by simpa using hb.le) hup).2

 /--
Defines `cubicBracketCheck` of type `Bool` by `decide (0≤A.lo ∧ 0<B.lo ∧ 0≤X.lo ∧
X.lo^3-A.lo*X.lo-B.lo≤0 ∧ 0≤X.hi^3-A.hi*X.hi-B.hi)`.

Use: `chebyshev2.Numerics.cubicBracketCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `positiveCubic a b∈X`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def cubicBracketCheck (A B X : IntervalRat) : Bool :=
  decide (0≤A.lo ∧ 0<B.lo ∧ 0≤X.lo ∧
    X.lo^3-A.lo*X.lo-B.lo≤0 ∧ 0≤X.hi^3-A.hi*X.hi-B.hi)

 /--
Membership in the specified domain/enclosure: `positiveCubic a b∈X`.

Use: `chebyshev2.Numerics.IntegerCertificate.cubicCheck_sound` uses this assertion to
establish the precise assertion is `R.Mem s (chebyshev2.Numerics.positiveCubic a b)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.positiveCubic_bracket` with the
arguments shown in the proof.
-/
theorem cubicBracketCheck_sound {A B X : IntervalRat} (h : cubicBracketCheck A B X=true)
    {a b : ℝ} (ha : a∈A) (hb : b∈B) : positiveCubic a b∈X := by
  -- Use the identities/estimates `chebyshev2.Numerics.positiveCubic_bracket` with the
  -- arguments shown in the proof.
  have hc : 0≤A.lo ∧ 0<B.lo ∧ 0≤X.lo ∧
      X.lo^3-A.lo*X.lo-B.lo≤0 ∧ 0≤X.hi^3-A.hi*X.hi-B.hi := of_decide_eq_true h
  have hA : (0:ℝ)≤A.lo := by exact_mod_cast hc.1
  have hB : (0:ℝ)<B.lo := by exact_mod_cast hc.2.1
  have hX : (0:ℝ)≤X.lo := by exact_mod_cast hc.2.2.1
  have hXu : (0:ℝ)≤X.hi := hX.trans (by exact_mod_cast X.le)
  have hl : (X.lo:ℝ)^3-(A.lo:ℝ)*X.lo-B.lo≤0 := by exact_mod_cast hc.2.2.2.1
  have hu : (0:ℝ)≤(X.hi:ℝ)^3-(A.hi:ℝ)*X.hi-B.hi := by exact_mod_cast hc.2.2.2.2
  have hbL := hb.1
  have hbU := hb.2
  exact positiveCubic_bracket (hA.trans ha.1) (hB.trans_le hb.1) hX hXu
    (by nlinarith [mul_le_mul_of_nonneg_right ha.1 hX])
    (by nlinarith [mul_le_mul_of_nonneg_right ha.2 hXu])

end
end chebyshev2.Numerics
