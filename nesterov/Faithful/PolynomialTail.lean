import nesterov.Faithful.PolynomialPositive

/-! Uniform polynomial perturbation estimates on a fixed compact interval. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Finset Filter Set
open scoped Topology

theorem polynomial_difference_bound {P Q : Polynomial ℝ} {N : ℕ} {K ε x R : ℝ}
    (hP : P.natDegree<N) (hQ : Q.natDegree<N) (hK : 0≤K) (hε : 0≤ε)
    (_hR : 0≤R) (hx : |x|≤R)
    (hcoeff : ∀ j : ℕ,j<N → |P.coeff j-Q.coeff j|≤K*ε) :
    |P.eval x-Q.eval x|≤K*ε*(∑ j∈range N,R^j) := by
  rw [eval_eq_sum_range' hP,eval_eq_sum_range' hQ,←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j hj
  rw [←sub_mul,abs_mul,abs_pow]
  exact mul_le_mul (hcoeff j (mem_range.mp hj))
    (pow_le_pow_left₀ (abs_nonneg x) hx j) (pow_nonneg (abs_nonneg x) j) (mul_nonneg hK hε)

/-- Retain the positive limit polynomial and absorb all higher-order
coefficient perturbations with the positive ε-linear term. -/
theorem eventually_positive_polynomial {P : ℝ→Polynomial ℝ} (N : ℕ)
    (hdegree : ∀ ε,(P ε).natDegree<N+2)
    (hcoeff : ∀ j,ContDiffWithinAt ℝ 1 (fun ε=>(P ε).coeff j) (Ici 0) 0)
    (hzero : (P 0).coeff 0=0) (hone : (P 0).coeff 1=0)
    (hpositive : ∀ x : ℝ,0<x → x≤2 → 0<(P 0).eval x)
    {A B : ℝ} (hA : 0<A) (hB : 0<B)
    (hlim0 : Tendsto (fun ε : ℝ=>(P ε).coeff 0/ε^3) (𝓝[>] (0:ℝ)) (𝓝 A))
    (hlim1 : Tendsto (fun ε : ℝ=>(P ε).coeff 1/ε) (𝓝[>] (0:ℝ)) (𝓝 B)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ x∈Icc (0:ℝ) 2,0<(P ε).eval x := by
  obtain ⟨K,hK,hbounds⟩ := coefficient_lipschitz_germ (N+2) hcoeff
  let ρ := min 1 (B/(4*((N:ℝ)*K+1)))
  have hNK : 0≤(N:ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK.le
  have hρ : 0<ρ := lt_min (by norm_num) (div_pos hB (by positivity))
  have hρ1 : ρ≤1 := min_le_left _ _
  have hρ2 : ρ≤2 := hρ1.trans (by norm_num)
  have hρB : (N:ℝ)*K*ρ≤B/2 := by
    have hh := (le_div_iff₀ (show 0<4*((N:ℝ)*K+1) by positivity)).mp
      (min_le_right (1:ℝ) (B/(4*((N:ℝ)*K+1))))
    change ρ*(4*((N:ℝ)*K+1))≤B at hh
    nlinarith [hρ.le]
  obtain ⟨xmin,hxmin,hmin⟩ := (isCompact_Icc : IsCompact (Icc ρ (2:ℝ))).exists_isMinOn ⟨ρ,le_rfl,hρ2⟩
    (P 0).continuous.continuousOn
  let m := (P 0).eval xmin
  have hm : 0<m := hpositive xmin (hρ.trans_le hxmin.1) hxmin.2
  let C := K*(∑ j∈range (N+2),(2:ℝ)^j)+1
  have hC : 0<C := by
    have hs : 0≤∑ j∈range (N+2),(2:ℝ)^j := sum_nonneg (fun _ _=>by positivity)
    dsimp [C]
    positivity
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<m/(2*C) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by positivity : (0:ℝ)<m/(2*C)))
  have ha0 := hlim0.eventually (lt_mem_nhds (show (0:ℝ)<A from hA))
  have ha1 := hlim1.eventually (lt_mem_nhds (show B/2<B by linarith))
  filter_upwards [hbounds,hsmall,ha0,ha1,self_mem_nhdsWithin] with ε hbound hsmallε h0 h1 hε
  change (0:ℝ)<ε at hε
  have hp0 : 0<(P ε).coeff 0 := by
    exact (div_pos_iff_of_pos_right (pow_pos hε 3)).mp h0
  have hp1 : (B/2)*ε≤(P ε).coeff 1 :=
    ((lt_div_iff₀ hε).mp h1).le
  intro x hx
  by_cases hnear : x≤ρ
  · have hQx : 0≤(P 0).eval x := by
      by_cases hx0 : x=0
      · have hv : (P 0).eval x=0 := by rw [hx0,←coeff_zero_eq_eval_zero,hzero]
        rw [hv]
      · exact (hpositive x (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2).le
    exact positive_of_coefficients (hdegree ε) (hdegree 0) hzero hone hQx hK.le hε hp0 hp1
      (fun j hj=>hbound (j+2) (by omega)) hx.1 (hnear.trans hρ1)
      ((mul_le_mul_of_nonneg_left hnear hNK).trans hρB)
  · have hQx : m≤(P 0).eval x := hmin ⟨(le_of_not_ge hnear),hx.2⟩
    have herr := polynomial_difference_bound (hdegree ε) (hdegree 0) hK.le hε.le (R:=2) (x:=x)
      (by norm_num) (by simpa only [abs_of_nonneg hx.1] using hx.2) hbound
    have hconst : K*ε*(∑ j∈range (N+2),(2:ℝ)^j)≤C*ε := by
      dsimp [C]
      nlinarith
    have hs := (lt_div_iff₀ (mul_pos (by norm_num) hC)).mp hsmallε
    have hdiff := (abs_le.mp herr).1
    linarith

end
end nesterov.Faithful
