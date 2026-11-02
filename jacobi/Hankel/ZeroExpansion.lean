import jacobi.Hankel.ZeroHolomorphy
import jacobi.Hankel.ZeroRemainder

/-!
Article: jacobi, Lemma E.1.
Use: squaring these actual branches gives the uniform inverse-square perturbation of the original reference spectrum in Lemma E.1.
-/
namespace jacobi.Hankel
noncomputable section
open Set Metric
set_option backward.isDefEq.respectTransparency false

/-- The original holomorphic complex-frequency Bessel zeros have the genuine uniform cubic reciprocal-grid expansion on one common order disk.
Use: squaring these actual branches gives the uniform inverse-square perturbation of the original reference spectrum in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: intersect the independently proved actual holomorphic zero disk with the actual uniform Hankel disk. Both constructions concern the same original normalized Bessel function. Its zero discharges the exact sine equation, its true cubic remainder supplies the residual, and the proved small-sine argument yields the uniform cubic correction. -/
theorem uniform_bessel_zero_expansion {a0 : ℝ} (ha0 : -1<a0) :
    ∃ r C : ℝ,∃ N : ℕ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 0<C ∧ 1≤N ∧
      ∀ k : ℕ,N≤k → ∃ u : ℂ → ℂ,DifferentiableOn ℂ u (ball (a0:ℂ) r) ∧
      ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖u a‖≤1/4 ∧
        jacobi.Bessel.normalized a ((frequencyGrid a k+u a)^2)=0 ∧
        ‖u a-besselCoefficient a/(2*frequencyGrid a k)‖≤C/(k:ℝ)^3 ∧
        ∀ ζ : ℂ,‖ζ‖≤1/4 → jacobi.Bessel.normalized a ((frequencyGrid a k+ζ)^2)=0 → ζ=u a := by
  -- The actual root and actual cubic error use the same original function, even if their auxiliary ray cutoffs differ.
  obtain ⟨R0,r0,hR0,N0,hr0,hr01,hra0,hN0,hzeros⟩ := uniform_bessel_holomorphic_zero_disks ha0
  obtain ⟨R,r,C,hR,N,hr,hr1,hra,hC,hN,herror⟩ := uniform_bessel_frequency_disks ha0
  let B : ℝ := (‖(a0:ℂ)‖+1)^2+1
  let E : ℝ := C*Real.exp 2/2
  let K : ℝ := B*(B+2)/2+2*B+2*E
  let D : ℝ := K^3+B*(B+2)*K/4+B*K^2/2+B*K/2+E
  have hB : 0<B := by dsimp [B]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨min r0 r,D,max N0 N,lt_min hr0 hr,(min_le_left _ _).trans hr01,
    (min_le_left _ _).trans_lt hra0,hD,hN0.trans (le_max_left _ _),fun k hk => ?_⟩
  have hk0 : N0≤k := (le_max_left N0 N).trans hk
  have hkN : N≤k := (le_max_right N0 N).trans hk
  obtain ⟨u,hu,hspec⟩ := hzeros k hk0
  refine ⟨u,hu.mono (ball_subset_ball (min_le_left _ _)),fun a ha => ?_⟩
  have ha0' : ‖a-(a0:ℂ)‖<r0 := ha.trans_le (min_le_left _ _)
  have ha' : ‖a-(a0:ℂ)‖<r := ha.trans_le (min_le_right _ _)
  obtain ⟨hsize,hzero,_hsimple,hunique⟩ := hspec a ha0'
  obtain ⟨_hc,hreal,hA,hbounds⟩ := herror a ha'
  have hk1 : 1≤(k:ℝ) := by exact_mod_cast hN.trans hkN
  have hζ := hbounds k hkN (u a) hsize
  have hgeom := (frequencyGrid_disk_geometry ha' hr1 hreal k hsize).1
  have hq := (frequencyGrid_disk_geometry ha' hr1 hreal k (by norm_num : ‖(0:ℂ)‖≤1/4)).1
  simp only [add_zero] at hq
  have he := frequencyNormalizer_quotient_bound ha' hr1 hζ.2.1 k
  have her : ‖frequencyError hR a (frequencyGrid a k+u a)/frequencyNormalizer a k‖≤E/(k:ℝ)^3 :=
    he.trans_eq (by dsimp [E]; ring)
  have hz : frequencyGrid a k+u a≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le zero_lt_one (hk1.trans (hgeom.trans (Complex.re_le_norm _))))
  have heq := (frequencyZeroEquation_zero_iff hR hA k (u a)).mpr hzero
  rw [(frequencyZeroEquation_expansion hR a k hz).1] at heq
  have hc : ‖besselCoefficient a‖≤B := besselCoefficient_unit_bound (ha'.le.trans hr1)
  have hresult := sine_zero_cubic hB.le hE.le hc hk1
    (hq.trans (Complex.re_le_norm _)) (hgeom.trans (Complex.re_le_norm _)) hsize her heq
  exact ⟨hsize,hzero,hresult,hunique⟩

end
end jacobi.Hankel
