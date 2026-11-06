import nesterov.Attainment.FiniteDual
import nesterov.Attainment.RootCount

/-! A finite normalized dual expansion has a real polynomial representative
of degree at most 2(D+M). Interior frequency zeros and their conjugates are
double roots, giving the article's sharp (D+M)/2 atom count. -/
noncomputable section
open Polynomial Set
open scoped BigOperators
namespace nesterov.Attainment
open Spectral

namespace FiniteDualExpansion
variable {M : StationaryMethod} {μ L : ℝ} {B : BoundaryDual M μ L} {N : ℕ}
variable (E : FiniteDualExpansion B N)

def polynomial : Polynomial ℝ :=
  ∑ j,C ((E.weight j : ℝ)/Real.sinh (E.lag j*(B.frame.center : ℝ))) *
    lagPolynomial M.memory N (radialPolynomial M.queryPolynomial (Closure.T M μ L))
      (radialPolynomial (M.normalizedPolynomial μ L) (Closure.T M μ L)) B.frame.center (E.lag j) (E.sign j)

def realSymbol (ω : ℝ) : ℝ :=
  ∑ j,((E.weight j : ℝ)/Real.sinh (E.lag j*(B.frame.center : ℝ))) *
    signedLagValue (amplitude M.queryPolynomial (Closure.T M μ L) ω)
      (amplitude (M.normalizedPolynomial μ L) (Closure.T M μ L) ω)
      B.frame.center ω (E.lag j) (E.sign j)

theorem polynomial_natDegree_le (hμL : μ < L) : E.polynomial.natDegree ≤ 2*(M.memory+N) := by
  have hu : (radialPolynomial M.queryPolynomial (Closure.T M μ L)).natDegree ≤ M.memory :=
    (radialPolynomial_natDegree_le _ _).trans M.queryPolynomial_natDegree_lt.le
  have hp : (radialPolynomial (M.normalizedPolynomial μ L) (Closure.T M μ L)).natDegree ≤ M.memory :=
    (radialPolynomial_natDegree_le _ _).trans (M.normalizedPolynomial_natDegree hμL).le
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomial,finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  have hb := (natDegree_C_mul_le ((E.weight j : ℝ)/Real.sinh (E.lag j*(B.frame.center : ℝ))) _).trans
    (lagPolynomial_natDegree_le hu hp (E.lag_le j) B.frame.center (E.sign j))
  exact coeff_eq_zero_of_natDegree_lt (hb.trans_lt hk)

theorem polynomial_phase (ω : ℝ) :
    ceval E.polynomial (polyak.Waves.z 0 ω)=
      polyak.Waves.z 0 ω^(M.memory+N)*(E.realSymbol ω : ℂ) := by
  have hu : (radialPolynomial M.queryPolynomial (Closure.T M μ L)).natDegree ≤ M.memory :=
    (radialPolynomial_natDegree_le _ _).trans M.queryPolynomial_natDegree_lt.le
  have hp : (radialPolynomial (M.normalizedPolynomial μ L) (Closure.T M μ L)).natDegree ≤ M.memory := by
    apply (radialPolynomial_natDegree_le _ _).trans
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [M.normalizedPolynomial_eq_sum]
    simp only [finsetSum_coeff,coeff_monomial]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (by omega)
  have he j := ceval_lagPolynomial_unit
    (radialPolynomial M.queryPolynomial (Closure.T M μ L))
    (radialPolynomial (M.normalizedPolynomial μ L) (Closure.T M μ L))
    hu hp (E.lag_le j) B.frame.center (E.sign j) ω
  simp_rw [ceval_radialPolynomial_phase] at he
  have hsum : ceval E.polynomial (polyak.Waves.z 0 ω)=
      ∑ j,ceval (C ((E.weight j : ℝ)/Real.sinh (E.lag j*(B.frame.center : ℝ))) *
        lagPolynomial M.memory N (radialPolynomial M.queryPolynomial (Closure.T M μ L))
          (radialPolynomial (M.normalizedPolynomial μ L) (Closure.T M μ L))
          B.frame.center (E.lag j) (E.sign j)) (polyak.Waves.z 0 ω) := by
    simp only [polynomial,ceval,Polynomial.map_sum,Polynomial.eval_finsetSum]
  rw [hsum]
  simp only [ceval_mul,ceval_C,he,realSymbol]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realSymbol_differentiable : Differentiable ℝ E.realSymbol := by
  unfold realSymbol signedLagValue amplitude
  simp only [Complex.normSq_apply]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem realSymbol_physical (c : Frequency) : E.realSymbol (Real.arccos c)=B.symbol c := by
  rw [E.symbol_eq]
  unfold realSymbol
  apply Finset.sum_congr rfl
  intro j _
  simp only [signedLagValue,lagA,lagB,g,skew,StationaryMethod.symbolPair_u,
    StationaryMethod.symbolPair_p,amplitude,polyak.Waves.z]
  ring

theorem realSymbol_nonpos {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) : E.realSymbol ω ≤ 0 := by
  let c : Frequency := ⟨Real.cos ω,Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have he := E.realSymbol_physical c
  have ha : Real.arccos (c:ℝ)=ω := Real.arccos_cos hω.1.le hω.2.le
  rw [ha] at he
  rw [he]
  exact B.nonpositive c

theorem polynomial_ne_zero (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L) : E.polynomial ≠ 0 := by
  have hn : B.symbol oneFrequency < 0 := dualHull_endpoint_neg _ _ _ _ _ _ _ oneFrequency
    (Or.inl rfl) (B.gap_endpoint_neg hμ hμL htq oneFrequency (Or.inl rfl)) B.mem_hull
  have hφ : E.realSymbol 0 < 0 := by
    have he := E.realSymbol_physical oneFrequency
    simpa only [oneFrequency,Real.arccos_one] using he.trans_lt hn
  intro hp
  have he := E.polynomial_phase 0
  rw [hp] at he
  simp only [ceval,Polynomial.map_zero,Polynomial.eval_zero,polyak.Waves.z,
    Complex.ofReal_zero,zero_mul,add_zero,Complex.exp_zero,one_pow,one_mul] at he
  have hz : E.realSymbol 0=0 := Complex.ofReal_injective he.symm
  linarith

include E in
/-- Sharp atom count for the common carrier, from any finite active-lag expansion. -/
theorem atom_count (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L) :
    B.zeroSet.ncard ≤ (M.memory+N)/2 := by
  classical
  have hF := B.zeroSet_finite hμ hμL htq
  let F := hF.toFinset
  have hFi : ∀ c∈F,-1 < (c:ℝ) ∧ (c:ℝ) < 1 := fun c hc =>
    B.zeroSet_interior hμ hμL htq (hF.mem_toFinset.mp hc)
  have hr : ∀ c∈F,ceval E.polynomial (frequencyPhase c)=0 ∧
      ceval E.polynomial.derivative (frequencyPhase c)=0 := by
    intro c hc
    have hci := hFi c hc
    have hω : Real.arccos (c:ℝ)∈Ioo (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr hci.2,Real.arccos_lt_pi.mpr hci.1⟩
    have hzero : E.realSymbol (Real.arccos c)=0 := by
      rw [E.realSymbol_physical]
      have hh : B.d.2 (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)=0 :=
        hF.mem_toFinset.mp hc
      exact congrArg Complex.re hh
    exact curve_double_root E.polynomial (M.memory+N) E.realSymbol E.polynomial_phase
      (fun ω hω => E.realSymbol_nonpos hω) hω (E.realSymbol_differentiable _) hzero
  have hh := half_circle_double_roots_card_le E.polynomial (E.polynomial_ne_zero hμ hμL htq) F hFi hr
  have hd := E.polynomial_natDegree_le hμL
  have hcard : F.card=B.zeroSet.ncard := by
    exact (Set.ncard_eq_toFinset_card _ hF).symm
  rw [hcard] at hh
  omega

end FiniteDualExpansion
end nesterov.Attainment
