import bezout.Comparisons.RootAsymptotics.FiniteSignal
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
Article: bezout, Proposition D.1, sharp LF/Prefix first-variation growth.
Use: proves both literal asymptotic ratios for actual physical signal matrices,
for every finite signal with equal positive endpoint energies. The argument
works on every divergent even-horizon sequence, hence on the LF dyadic sequence.
Proof: divide the exact endpoint-plus-bulk sandwiches by their positive common
scale and leading horizon power, then take ratios and the nonnegative square root.
-/

namespace bezout.Comparisons.RootAsymptotics
noncomputable section
open Filter Topology Asymptotics Channel

variable {I : chebyshev1.SpectralInterval} {J : Type*} [Fintype J] [DecidableEq J]

/-- Dividing a two-sided physical estimate by a positive common scale is legitimate. -/
theorem scaled_bounds {f b c r : ℝ} (hc : 0<c) (hb : b≤f ∧ f≤b+c*r) :
    b/c≤f/c ∧ f/c≤b/c+r := by
  constructor
  · exact div_le_div_of_nonneg_right hb.1 hc.le
  · calc
      _ ≤ (b+c*r)/c := div_le_div_of_nonneg_right hb.2 hc.le
      _ = _ := by field_simp

/-- A normalized endpoint sandwich transfers its limit through a vanishing bulk remainder. -/
theorem sandwich_limit {f b r : ℕ → ℝ} {a : ℝ}
    (hb : Tendsto b atTop (𝓝 a)) (hr : Tendsto r atTop (𝓝 0))
    (hf : ∀ k,b k≤f k ∧ f k≤b k+r k) : Tendsto f atTop (𝓝 a) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hb
    (by simpa only [add_zero] using hb.add hr)
    (fun k => (hf k).1) (fun k => (hf k).2)

/-- All four normalized physical matrix energies have their sharp leading coefficients. -/
theorem matrix_normalized_limits (S : FiniteSignal I J) (N : ℕ → ℕ)
    (e : (k : ℕ) → Equiv.Perm (Fin (N k))) (hN : Tendsto N atTop atTop)
    (hpos : ∀ k,0<N k) (heven : ∀ k,Even (N k)) :
    Tendsto (fun k => rectangularNorm (rootMatrix S (N k) (e k))^2/
      (scaleSq I (N k)*(N k:ℝ)^4)) atTop (𝓝 (2*S.mass/3)) ∧
    Tendsto (fun k => rectangularHsSq (rootMatrix S (N k) (e k))/
      (scaleSq I (N k)*(N k:ℝ)^4)) atTop (𝓝 (4*S.mass/3)) ∧
    Tendsto (fun k => rectangularNorm (prefixMatrix S (N k))^2/
      (scaleSq I (N k)*(N k:ℝ)^3)) atTop (𝓝 (8*S.mass/3)) ∧
    Tendsto (fun k => rectangularHsSq (prefixMatrix S (N k))/
      (scaleSq I (N k)*(N k:ℝ)^3)) atTop (𝓝 (8*S.mass/3)) := by
  have hi : Tendsto (fun k => 1/(N k:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hi2 : Tendsto (fun k => (1/(N k:ℝ))^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2≠0)] using hi.pow 2
  have hroot : Tendsto (fun k => S.mass*(2/3+(4/3:ℝ)*(1/(N k:ℝ))^2))
      atTop (𝓝 (2*S.mass/3)) := by
    simpa only [mul_zero,add_zero,show S.mass*(2/3:ℝ)=2*S.mass/3 by ring] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2/3:ℝ)) atTop (𝓝 _)).add
        (hi2.const_mul (4/3:ℝ))).const_mul S.mass
  have hrootHS : Tendsto (fun k => S.mass*(4/3+(2/3:ℝ)*(1/(N k:ℝ))^2))
      atTop (𝓝 (4*S.mass/3)) := by
    simpa only [mul_zero,add_zero,show S.mass*(4/3:ℝ)=4*S.mass/3 by ring] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (4/3:ℝ)) atTop (𝓝 _)).add
        (hi2.const_mul (2/3:ℝ))).const_mul S.mass
  have hprefix : Tendsto (fun k => 2*S.mass*(4/3-1/(N k:ℝ)+(2/3:ℝ)*(1/(N k:ℝ))^2))
      atTop (𝓝 (8*S.mass/3)) := by
    simpa only [sub_zero,mul_zero,add_zero,show 2*S.mass*(4/3:ℝ)=8*S.mass/3 by ring] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (4/3:ℝ)) atTop (𝓝 _)).sub hi).add
        (hi2.const_mul (2/3:ℝ))).const_mul (2*S.mass)
  have hr := hi2.const_mul (rootBulkConstant S)
  have hp := hi2.const_mul (prefixBulkConstant S)
  simp only [mul_zero] at hr hp
  have rootBound (k : ℕ) := root_matrix_bounds S (N k) (heven k) (e k)
  have prefixBound (k : ℕ) := prefix_matrix_bounds S (N k) (hpos k) (heven k)
  have hscale (k : ℕ) (p : ℕ) : 0<scaleSq I (N k)*(N k:ℝ)^p := by
    have hn : (0:ℝ)<N k := by exact_mod_cast hpos k
    exact mul_pos (scaleSq_pos I _) (pow_pos hn _)
  have hn (k : ℕ) : (N k:ℝ)≠0 := by exact_mod_cast (ne_of_gt (hpos k))
  have hs (k : ℕ) : scaleSq I (N k)≠0 := ne_of_gt (scaleSq_pos I _)
  have rootRewrite (k : ℕ) (a b : ℝ) :
      S.mass*scaleSq I (N k)*((a*(N k:ℝ)^4+b*(N k:ℝ)^2)/3)/
        (scaleSq I (N k)*(N k:ℝ)^4)=S.mass*(a/3+(b/3)*(1/(N k:ℝ))^2) := by
    field_simp [hn k,hs k]
  have prefixRewrite (k : ℕ) :
      2*S.mass*scaleSq I (N k)*chebyshev1.Prefix.shape (N k)/
        (scaleSq I (N k)*(N k:ℝ)^3)=
        2*S.mass*(4/3-1/(N k:ℝ)+(2/3:ℝ)*(1/(N k:ℝ))^2) := by
    unfold chebyshev1.Prefix.shape
    field_simp [hn k,hs k]
    ring
  have rb (k : ℕ) (f : ℝ) (a b : ℝ)
      (hb : S.mass*scaleSq I (N k)*((a*(N k:ℝ)^4+b*(N k:ℝ)^2)/3)≤f ∧
        f≤S.mass*scaleSq I (N k)*((a*(N k:ℝ)^4+b*(N k:ℝ)^2)/3)+
          scaleSq I (N k)*rootBulkConstant S*(N k:ℝ)^2) :
      S.mass*(a/3+(b/3)*(1/(N k:ℝ))^2)≤f/(scaleSq I (N k)*(N k:ℝ)^4) ∧
      f/(scaleSq I (N k)*(N k:ℝ)^4)≤S.mass*(a/3+(b/3)*(1/(N k:ℝ))^2)+
        rootBulkConstant S*(1/(N k:ℝ))^2 := by
    have hh := scaled_bounds (f := f)
      (b := S.mass*scaleSq I (N k)*((a*(N k:ℝ)^4+b*(N k:ℝ)^2)/3))
      (hscale k 4) (r := rootBulkConstant S*(1/(N k:ℝ))^2) ?_
    · rw [rootRewrite k a b] at hh
      exact hh
    · convert hb using 1; field_simp [hn k]
  have pb (k : ℕ) (f : ℝ)
      (hb : 2*S.mass*scaleSq I (N k)*chebyshev1.Prefix.shape (N k)≤f ∧
        f≤2*S.mass*scaleSq I (N k)*chebyshev1.Prefix.shape (N k)+
          scaleSq I (N k)*prefixBulkConstant S*(N k:ℝ)) :
      2*S.mass*(4/3-1/(N k:ℝ)+(2/3:ℝ)*(1/(N k:ℝ))^2)≤
        f/(scaleSq I (N k)*(N k:ℝ)^3) ∧
      f/(scaleSq I (N k)*(N k:ℝ)^3)≤
        2*S.mass*(4/3-1/(N k:ℝ)+(2/3:ℝ)*(1/(N k:ℝ))^2)+
          prefixBulkConstant S*(1/(N k:ℝ))^2 := by
    have hh := scaled_bounds (f := f)
      (b := 2*S.mass*scaleSq I (N k)*chebyshev1.Prefix.shape (N k))
      (hscale k 3) (r := prefixBulkConstant S*(1/(N k:ℝ))^2) ?_
    · rw [prefixRewrite k] at hh
      exact hh
    · convert hb using 1; field_simp [hn k]
  refine ⟨sandwich_limit hroot hr (fun k => rb k _ 2 4 (rootBound k).1),
    sandwich_limit hrootHS hr (fun k => rb k _ 4 2 (rootBound k).2),
    sandwich_limit hprefix hp (fun k => pb k _ (prefixBound k).1),
    sandwich_limit hprefix hp (fun k => pb k _ (prefixBound k).2)⟩

/-- The physical root/Prefix operator norm ratio has the sharp square-root growth. -/
theorem operator_ratio_limit (S : FiniteSignal I J) (N : ℕ → ℕ)
    (e : (k : ℕ) → Equiv.Perm (Fin (N k))) (hN : Tendsto N atTop atTop)
    (hpos : ∀ k,0<N k) (heven : ∀ k,Even (N k)) :
    Tendsto (fun k => (rectangularNorm (rootMatrix S (N k) (e k))/
      rectangularNorm (prefixMatrix S (N k)))/(Real.sqrt (N k)/2)) atTop (𝓝 1) := by
  have hm := matrix_normalized_limits S N e hN hpos heven
  have hlim := hm.1.div hm.2.2.1 (by have := S.mass_pos; positivity)
  have hlim' : Tendsto (fun k => Real.sqrt
      ((rectangularNorm (rootMatrix S (N k) (e k))^2/(scaleSq I (N k)*(N k:ℝ)^4))/
       (rectangularNorm (prefixMatrix S (N k))^2/(scaleSq I (N k)*(N k:ℝ)^3))))
      atTop (𝓝 (1/2:ℝ)) := by
    convert hlim.sqrt using 1
    have hw := ne_of_gt S.mass_pos
    field_simp
    norm_num
  have hh := hlim'.const_mul 2
  norm_num at hh
  apply hh.congr'
  exact Eventually.of_forall (fun k => by
    dsimp only [Pi.div_apply]
    have hn : (0:ℝ)<N k := by exact_mod_cast hpos k
    have hs := scaleSq_pos I (N k)
    have he := Real.sqrt_pos.mpr hn
    have hA : 0≤rectangularNorm (rootMatrix S (N k) (e k)) := norm_nonneg _
    have hB : 0≤rectangularNorm (prefixMatrix S (N k)) := norm_nonneg _
    have hsq : (rectangularNorm (rootMatrix S (N k) (e k))^2/(scaleSq I (N k)*(N k:ℝ)^4))/
        (rectangularNorm (prefixMatrix S (N k))^2/(scaleSq I (N k)*(N k:ℝ)^3))=
        ((rectangularNorm (rootMatrix S (N k) (e k))/
          rectangularNorm (prefixMatrix S (N k)))/Real.sqrt (N k))^2 := by
      by_cases hb : rectangularNorm (prefixMatrix S (N k))=0
      · simp [hb]
      · field_simp [hb,ne_of_gt hs,ne_of_gt hn,ne_of_gt he]
        rw [Real.sq_sqrt hn.le]
    rw [hsq,Real.sqrt_sq (div_nonneg (div_nonneg hA hB) he.le)]
    ring)

/-- The physical squared-HS ratio has the sharp linear growth. -/
theorem hs_ratio_limit (S : FiniteSignal I J) (N : ℕ → ℕ)
    (e : (k : ℕ) → Equiv.Perm (Fin (N k))) (hN : Tendsto N atTop atTop)
    (hpos : ∀ k,0<N k) (heven : ∀ k,Even (N k)) :
    Tendsto (fun k => (rectangularHsSq (rootMatrix S (N k) (e k))/
      rectangularHsSq (prefixMatrix S (N k)))/((N k:ℝ)/2)) atTop (𝓝 1) := by
  have hm := matrix_normalized_limits S N e hN hpos heven
  have hh := (hm.2.1.div hm.2.2.2 (by have := S.mass_pos; positivity)).const_mul 2
  have hvalue : (2:ℝ)*(4*S.mass/3/(8*S.mass/3))=1 := by
    field_simp [ne_of_gt S.mass_pos]
    ring
  rw [hvalue] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun k => by
    dsimp only [Pi.div_apply]
    have hn : (N k:ℝ)≠0 := by exact_mod_cast (ne_of_gt (hpos k))
    by_cases hb : rectangularHsSq (prefixMatrix S (N k))=0
    · simp [hb]
    · field_simp [hb,ne_of_gt (scaleSq_pos I (N k)),hn]
    )

/-- Positive dyadic horizons used by the literal LF construction. -/
def dyadicHorizon (k : ℕ) : ℕ := 2^(k+1)

/-- Dyadic horizons diverge. -/
theorem dyadicHorizon_tendsto : Tendsto dyadicHorizon atTop atTop := by
  apply tendsto_atTop_mono (fun k => Nat.le_of_lt (Nat.lt_two_pow_self (n := k+1)))
  exact tendsto_add_atTop_nat 1

/-- The actual LF/Prefix operator norm ratio is asymptotic to sqrt(N)/2. -/
theorem lf_operator_isEquivalent (S : FiniteSignal I J) :
    (fun k => rectangularNorm (rootMatrix S (dyadicHorizon k) (Roots.dyadicPermutation (k+1)))/
      rectangularNorm (prefixMatrix S (dyadicHorizon k))) ~[atTop]
        (fun k => Real.sqrt (dyadicHorizon k)/2) := by
  apply (isEquivalent_iff_tendsto_one ?_).mpr
  · exact operator_ratio_limit S dyadicHorizon (fun k => Roots.dyadicPermutation (k+1))
      dyadicHorizon_tendsto (fun k => by simp [dyadicHorizon])
      (fun k => ⟨2^k,by simp [dyadicHorizon,pow_succ]; omega⟩)
  · exact Eventually.of_forall (fun k => by
      have hn : (0:ℝ)<dyadicHorizon k := by simp [dyadicHorizon]
      exact div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hn)) (by norm_num))

/-- The actual LF/Prefix squared-HS ratio is asymptotic to N/2. -/
theorem lf_hs_isEquivalent (S : FiniteSignal I J) :
    (fun k => rectangularHsSq (rootMatrix S (dyadicHorizon k) (Roots.dyadicPermutation (k+1)))/
      rectangularHsSq (prefixMatrix S (dyadicHorizon k))) ~[atTop]
        (fun k => (dyadicHorizon k:ℝ)/2) := by
  apply (isEquivalent_iff_tendsto_one ?_).mpr
  · exact hs_ratio_limit S dyadicHorizon (fun k => Roots.dyadicPermutation (k+1))
      dyadicHorizon_tendsto (fun k => by simp [dyadicHorizon])
      (fun k => ⟨2^k,by simp [dyadicHorizon,pow_succ]; omega⟩)
  · exact Eventually.of_forall (fun k => by simp [dyadicHorizon])

end
end bezout.Comparisons.RootAsymptotics
