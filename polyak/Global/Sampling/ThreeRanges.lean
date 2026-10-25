import polyak.Global.Sampling.QuadraticCutoff

/-! The three disjoint lag ranges in Appendix E give one positive margin
for every nonzero integer lag, with no finite lag truncation. -/
noncomputable section
namespace polyak.Global.Sampling

def samplingPolynomial (c c0 M m R : ℝ) : ℝ→ℝ :=
  cutoffPolynomial (c*c0) (6*M*m) (8*M^2*m+R)

theorem three_range_margin {c c0 M m R ε a : ℝ}
    (hc : 0<c) (hc0 : 0<c0) (hm : 0≤m) (hR : 0≤R)
    (hε : 0<ε) (ha : 0<a)
    (hat μ out D : ℤ→ℝ)
    (hhat : ∀n,0≤hat n ∧ hat n≤1)
    (hgain : ∀n:ℤ,c*min (ε^2*(n:ℝ)^2) 1≤1-hat n)
    (hμ : ∀n,0≤μ n)
    (hsmooth : ∀n,hat n*μ n+(1-hat n)*c0-D 0-3*D n-R*ε^2≤out n)
    (hDfine : ∀n,D n≤2*M*m*ε^2*(|(n:ℝ)|+M))
    (hDcoarse : ∀n,D n≤M*ε)
    (hhigh : 4*M*ε+R*ε^2≤c*c0/2)
    (hlow : ∀n:ℤ,n≠0→|(n:ℝ)|<(lagCutoff (c*c0) (6*M*m) (8*M^2*m+R):ℝ)→
      a≤μ n ∧ 1/2≤hat n ∧ D 0+3*D n+R*ε^2≤a/4) :
    ∃δ:ℝ,0<δ ∧ ∀n:ℤ,n≠0→δ≤out n := by
  let N:=lagCutoff (c*c0) (6*M*m) (8*M^2*m+R)
  have hA : 0<c*c0 := mul_pos hc hc0
  have hC : 0≤8*M^2*m+R := by positivity
  have hcut:=lagCutoff_properties (B:=6*M*m) hA hC
  let P:=samplingPolynomial c c0 M m R
  have hP : 0<P N := hcut.2.2.1
  let δ:=min (c*c0/2) (min (ε^2*P N) (a/4))
  refine ⟨δ,by dsimp [δ]; positivity,?_⟩
  intro n hn
  have hh:=hhat n
  have hnonneg : 0≤hat n*μ n:=mul_nonneg hh.1 (hμ n)
  have hg:=hgain n
  have hs:=hsmooth n
  by_cases hlarge : 1≤ε*|(n:ℝ)|
  · have hsq : 1≤ε^2*(n:ℝ)^2 := by nlinarith [sq_abs (n:ℝ),sq_nonneg (ε*|(n:ℝ)|-1)]
    rw [min_eq_right hsq] at hg
    have hgc:=mul_le_mul_of_nonneg_right hg hc0.le
    have hD0:=hDcoarse 0
    have hDn:=hDcoarse n
    have hd : δ≤c*c0/2:=min_le_left _ _
    linarith
  · by_cases hmedium : (N:ℝ)≤|(n:ℝ)|
    · have hsq : ε^2*(n:ℝ)^2≤1 := by
        have hh0 : 0≤ε*|(n:ℝ)|:=mul_nonneg hε.le (abs_nonneg _)
        nlinarith [sq_abs (n:ℝ)]
      rw [min_eq_left hsq] at hg
      have hgc:=mul_le_mul_of_nonneg_right hg hc0.le
      have hD0:=hDfine 0
      have hDn:=hDfine n
      simp only [Int.cast_zero,abs_zero,zero_add] at hD0
      have hp:=hcut.2.2.2 |(n:ℝ)| hmedium
      change P N≤P |(n:ℝ)| at hp
      have hpm:=mul_le_mul_of_nonneg_left hp (sq_nonneg ε)
      have hd : δ≤ε^2*P N:=(min_le_right _ _).trans (min_le_left _ _)
      dsimp [P,samplingPolynomial,cutoffPolynomial] at hpm hd
      rw [sq_abs] at hpm
      nlinarith only [hs,hnonneg,hgc,hDn,hD0,hpm,hd]
    · have hsmall : |(n:ℝ)|<(N:ℝ):=lt_of_not_ge hmedium
      obtain ⟨hμa,hha,herr⟩:=hlow n hn hsmall
      have hprod : a/2≤hat n*μ n := by
        have h1:=mul_le_mul_of_nonneg_left hμa hh.1
        have h2:=mul_le_mul_of_nonneg_right hha ha.le
        nlinarith
      have hpositive : 0≤(1-hat n)*c0:=mul_nonneg (sub_nonneg.mpr hh.2) hc0.le
      have hd : δ≤a/4:=(min_le_right _ _).trans (min_le_right _ _)
      linarith

end polyak.Global.Sampling
