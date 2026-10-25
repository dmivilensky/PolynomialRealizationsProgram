import polyak.Farey.Certificates.Indexed
import polyak.Levels.Program.ChebyshevLag

/-! Signed Chebyshev polynomials give strict certificates on the entire
closed frequency interval; positive gamma closes both endpoints. -/
noncomputable section
namespace polyak.Farey.Certificates
open Levels Set
open Spectral (chebT chebU)
open scoped BigOperators

def signedLagPolynomial (q:General.Tuning) (n:ℤ) (c:ℝ) : ℝ:=
  q.Xi c*(1-chebT n.natAbs c)-
    (n.sign:ℝ)*(1-c^2)*chebU (n.natAbs-1) c

theorem minimizer_factor (q:General.Tuning) (ω:Frequency)
    (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    (tuningCurve q).minimizer ω=Real.sin (q.angle ω)/Real.sin (ω:ℝ)*q.Xi (Real.cos (ω:ℝ)) := by
  have hs : Real.sin (ω:ℝ)≠0:=(Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'
  have ht : Real.sin (q.angle ω)≠0:=
    (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2).ne'
  have hh:=(div_eq_div_iff ht hs).mp (q.cot_angle hω)
  change Real.cos (q.angle ω)=_
  field_simp
  nlinarith only [hh]

theorem lag_polynomial_factor (q:General.Tuning) (n:ℤ) (hn:n≠0) (ω:Frequency)
    (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    (tuningCurve q).lag n ω=Real.sin (q.angle ω)/Real.sin (ω:ℝ)*
      signedLagPolynomial q n (Real.cos (ω:ℝ)) := lag_chebyshev q n hn ω hω

variable {I:Type*} [Fintype I]

def indexedPolynomial (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ c:ℝ) : ℝ:=
  (∑i,a i*signedLagPolynomial q (n i) c)+γ*q.Xi c

theorem indexed_polynomial_factor (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ:ℝ)
    (hn:∀i,n i≠0) (ω:Frequency) (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    (∑i,a i*(tuningCurve q).lag (n i) ω)+γ*(tuningCurve q).minimizer ω=
      Real.sin (q.angle ω)/Real.sin (ω:ℝ)*indexedPolynomial q n a γ (Real.cos (ω:ℝ)) := by
  simp_rw [lag_polynomial_factor q _ (hn _) ω hω]
  rw [minimizer_factor q ω hω]
  unfold indexedPolynomial
  rw [mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem indexed_negative_endpoints (Θ:Curve) (n:I→ℤ) (a:I→ℝ) {γ:ℝ}
    (ha:∀i,0≤a i) (hγ:0<γ) :
    ((∑i,a i*Θ.lag (n i) frequencyZero)+γ*Θ.minimizer frequencyZero<0) ∧
      ((∑i,a i*Θ.lag (n i) frequencyPi)+γ*Θ.minimizer frequencyPi<0) := by
  constructor
  · simpa only [Curve.lag_at_zero,mul_zero,Finset.sum_const_zero,
      Curve.minimizer_at_zero,mul_neg,mul_one,zero_add] using neg_neg_of_pos hγ
  · have hs : (∑i,a i*Θ.lag (n i) frequencyPi)≤0 :=
      Finset.sum_nonpos (fun i _=>mul_nonpos_of_nonneg_of_nonpos (ha i) (Θ.lag_at_pi_nonpos _))
    rw [Θ.minimizer_at_pi]
    nlinarith

theorem indexed_polynomial_negative (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) {γ:ℝ}
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,indexedPolynomial q n a γ c<0) :
    ∀ω:Frequency,(∑i,a i*(tuningCurve q).lag (n i) ω)+γ*(tuningCurve q).minimizer ω<0 := by
  intro ω
  by_cases hz:ω=frequencyZero
  · subst ω
    exact (indexed_negative_endpoints _ n a ha hγ).1
  by_cases hp:ω=frequencyPi
  · subst ω
    exact (indexed_negative_endpoints _ n a ha hγ).2
  have hω : 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi := by
    constructor
    · exact lt_of_le_of_ne ω.property.1 (fun h=>hz (Subtype.ext h.symm))
    · exact lt_of_le_of_ne ω.property.2 (fun h=>hp (Subtype.ext h))
  rw [indexed_polynomial_factor q n a γ hn ω hω]
  exact mul_neg_of_pos_of_neg
    (div_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2)
      (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2))
    (hP _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)

theorem polynomial_rate_lt_one (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) {γ:ℝ}
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,indexedPolynomial q n a γ c<0) : q.rate<1 :=
  indexed_negative_rate_lt_one q n a γ hn ha hγ.le
    (indexed_polynomial_negative q n a hn ha hγ hP)

theorem polynomial_strict_symbol (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) {γ:ℝ}
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,indexedPolynomial q n a γ c<0) :
    ∃S:StrictSymbol (tuningCurve q) nonzeroLags,
      S.symbol=indexedSymbol (tuningCurve q) n a γ hn ha hγ.le := by
  let S:=indexedSymbol (tuningCurve q) n a γ hn ha hγ.le
  have hS:∀ω,S.eval ω<0:=by
    intro ω
    rw [indexedSymbol_eval]
    exact indexed_polynomial_negative q n a hn ha hγ hP ω
  obtain ⟨ω,_hω,hmax⟩:=isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    S.continuous_eval.continuousOn
  refine ⟨⟨S,-S.eval ω,neg_pos.mpr (hS ω),?_⟩,rfl⟩
  intro x
  simpa only [neg_neg] using (show S.eval x≤S.eval ω from hmax (Set.mem_univ x))

end polyak.Farey.Certificates
