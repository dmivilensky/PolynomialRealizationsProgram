import polyak.FareyPlateau.Ray.SecondMoment
import polyak.FareyPlateau.Ray.LatticeCost

/-! Exact sharpness and equality support for the lattice moment. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open scoped BigOperators Classical

theorem SourceCertificate.moment_cost_identity {j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (C : SourceCertificate j k b D) (hb : (b*j)%k=1)
    (hbar : edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    curvatureMoment C.lag C.weight
        (edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D)-
      oneMass k b C.lag C.weight*(k:ℝ)^2*t*(1-t)=
      ∑i,C.weight i*latticeCost k b n₁ (C.lag i) t := by
  let bar := edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D
  let K := (k:ℝ)^2*t*(1-t)
  let ρ := (n₁:ℝ)+(k:ℝ)-t*k
  have hp (i) : C.weight i*latticeCost k b n₁ (C.lag i) t=
      C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)-bar)-
      (if C.lag i%k=b%k then C.weight i else 0)*K-
      ((if C.lag i%k=b%k then C.weight i*(C.lag i:ℝ) else 0)*2-
        C.weight i*(C.lag i:ℝ)-(if C.lag i%k=b%k then C.weight i else 0)*bar)*ρ := by
    dsimp [bar,K,ρ,latticeCost]
    rw [hbar]
    by_cases hi : C.lag i%k=b%k <;> simp [hi] <;> ring
  have hsum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _=>hp i)
  have hμ : (∑i,if C.lag i%k=b%k then C.weight i else 0)=oneMass k b C.lag C.weight := by
    unfold oneMass oneClass
    rw [Finset.sum_filter]
  have hM : (∑i,if C.lag i%k=b%k then C.weight i*(C.lag i:ℝ) else 0)=
      oneMoment k b C.lag C.weight := by
    unfold oneMoment oneClass
    rw [Finset.sum_filter]
  simp only [Finset.sum_sub_distrib,←Finset.sum_mul,hμ,hM] at hsum
  change (∑i,C.weight i*latticeCost k b n₁ (C.lag i) t)=
    curvatureMoment C.lag C.weight bar-oneMass k b C.lag C.weight*K-
      (oneMoment k b C.lag C.weight*2-firstMoment C.lag C.weight-
        oneMass k b C.lag C.weight*bar)*ρ at hsum
  have hz : oneMoment k b C.lag C.weight*2-firstMoment C.lag C.weight-
      oneMass k b C.lag C.weight*bar=0 := by
    have ht := admissible_moment_balance hb C.admissible
    change 2*oneMoment k b C.lag C.weight-firstMoment C.lag C.weight=
      bar*oneMass k b C.lag C.weight at ht
    nlinarith only [ht]
  rw [hz,zero_mul,sub_zero] at hsum
  dsimp [bar,K] at hsum
  linear_combination -hsum

theorem SourceCertificate.sharp_moment {j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (C : SourceCertificate j k b D) (hk : 0<k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    oneMass k b C.lag C.weight*(k:ℝ)^2*t*(1-t)≤
      curvatureMoment C.lag C.weight
        (edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D) := by
  have hcost := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>mul_nonneg (C.admissible.positive i).le
    (latticeCost_nonneg hk ht0 ht1 hn₁ (C.admissible.nonzero i) (C.admissible.positions i)))
  rw [←C.moment_cost_identity hb hbar] at hcost
  linarith

theorem SourceCertificate.sharp_moment_eq_iff {j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (C : SourceCertificate j k b D) (hk : 0<k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    curvatureMoment C.lag C.weight
        (edgeSlope (General.Regions.rationalAngle j k) (Real.pi/k) D)=
      oneMass k b C.lag C.weight*(k:ℝ)^2*t*(1-t) ↔
      ∀i,C.lag i=n₁ ∨ C.lag i=n₁+k := by
  have hnonneg (i : Fin C.card) : 0≤C.weight i*latticeCost k b n₁ (C.lag i) t :=
    mul_nonneg (C.admissible.positive i).le
      (latticeCost_nonneg hk ht0 ht1 hn₁ (C.admissible.nonzero i) (C.admissible.positions i))
  have hid := C.moment_cost_identity hb hbar
  constructor
  · intro heq
    rw [heq,sub_self] at hid
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>hnonneg i)).mp hid.symm
    intro i
    have hcost : latticeCost k b n₁ (C.lag i) t=0 :=
      (mul_eq_zero.mp (hz i (Finset.mem_univ _))).resolve_left (C.admissible.positive i).ne'
    exact (latticeCost_eq_zero_iff hk ht0 ht1 hn₁ (C.admissible.nonzero i)
      (C.admissible.positions i)).mp hcost
  · intro heq
    have hz : (∑i,C.weight i*latticeCost k b n₁ (C.lag i) t)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [(latticeCost_eq_zero_iff hk ht0 ht1 hn₁ (C.admissible.nonzero i)
        (C.admissible.positions i)).mpr (heq i),mul_zero]
    rw [hz] at hid
    linarith

end polyak.FareyPlateau.Ray
