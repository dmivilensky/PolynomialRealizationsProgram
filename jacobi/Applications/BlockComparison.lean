import jacobi.Applications.BlockInfimum
import jacobi.Applications.GainLimits

/-!
Article: jacobi, Theorem 5.1.
The complete U-fibre gain infimum and the original canonical block have
the same leading constant. The lower bound uses every original fibre
member and the proved continuum optimum; the upper bound is attained by
the actual uniform chain. Their common count is exactly 2*m+2.
Use: Article checks the sharp original method comparison directly.
-/
namespace jacobi.Applications
noncomputable section
open Filter Real Set jacobi.Variational
open scoped Topology ENNReal
set_option maxHeartbeats 1000000

/-- The genuine canonical block gain has the exact sharp leading coefficient at the original even application count.
Use: block_optimal_gain_limit supplies a matching upper bound for the whole original block class; canonical_block_gain_ratio compares it with Nesterov.
Article: jacobi, Theorem 5.1.
Proof: divide the exact finite squared gain by k^3. All three finite corrections are inverse powers of the actual diverging horizon. The continuous nonnegative square root recovers the true gain. -/
theorem canonical_block_gain_limit :
    Tendsto (fun m:ℕ=>unitSpectralGain (blockMethod (uniformUChain m)).realization (2*m+2)/
      ((2*m+2:ℕ):ℝ)^((3:ℝ)/2)) atTop (𝓝 (1/sqrt 15)) := by
  -- The complete finite formula, including its inverse-horizon term, is used before taking the limit.
  have hk:Tendsto (fun m:ℕ=>((2*m+2:ℕ):ℝ)) atTop atTop:=by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro m
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hi:=tendsto_inv_atTop_zero.comp hk
  have hs:Tendsto (fun m:ℕ=>(unitSpectralGain (blockMethod (uniformUChain m)).realization (2*m+2))^2/
      ((2*m+2:ℕ):ℝ)^3) atTop (𝓝 (1/15:ℝ)):=by
    have h:=(((tendsto_const_nhds (x:=(1/15:ℝ))).add ((hi.pow 2).const_mul (1/2:ℝ))).add
      (hi.pow 3)).sub ((hi.pow 4).const_mul (16/15:ℝ))
    norm_num at h
    apply (tendsto_congr (fun m=>?_)).mpr h
    rw [uniformU_even_block_gain_square]
    push_cast
    have hn:((2*m+2:ℕ):ℝ)≠0:=by positivity
    field_simp
  have he:sqrt (1/15:ℝ)=1/sqrt 15:=by rw [sqrt_div (by norm_num),sqrt_one]
  rw [← he]
  exact gain_limit_of_square (fun _=>unitSpectralGain_nonneg _ _) (fun _=>by positivity) hs

/-- The true full-fibre gain optimum has exactly the source sharp asymptotic constant.
Use: Article checks the infimum over all U-fibre realizations, retaining the complete original competitor set.
Article: jacobi, Theorem 5.1.
Proof: the actual full-fibre U-energy infimum tends to 2/15 after m^3 normalization. Every original block gain dominates its endpoint energy 4*E(J)+m+2. Since m/(2m+2) tends to 1/2, this lower comparison tends to 1/sqrt(15). The genuine canonical block has the same limit and bounds the full infimum from above. -/
theorem block_optimal_gain_limit :
    Tendsto (fun n:ℕ=>blockGainInfimum (n+1)/((2*(n+1)+2:ℕ):ℝ)^((3:ℝ)/2))
      atTop (𝓝 (1/sqrt 15)) := by
  -- No minimizing sequence is restricted to persymmetric chains: the lower bound is for the full original fibre.
  let L (n:ℕ):ℝ:=(fibreEnergyInfimum (jacobi.Jacobi.nodes (1/2) (1/2)
    (by norm_num) (by norm_num) (n+1))).toReal
  let k (n:ℕ):ℝ:=((2*(n+1)+2:ℕ):ℝ)
  have hL:Tendsto L atTop (𝓝 (2/15:ℝ)):=by
    have h:=(ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp jacobi.Counterexample.u_base_energy_limit
    simpa only [L,Function.comp_def,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2/15)] using h
  have hk:Tendsto k atTop atTop:=by
    dsimp [k]
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hi:=tendsto_inv_atTop_zero.comp hk
  have hm:Tendsto (fun n:ℕ=>(n+1:ℝ)/k n) atTop (𝓝 (1/2:ℝ)):=by
    have h:=(jacobi.Reference.shifted_nat_ratio 1 2).const_mul (1/2:ℝ)
    simp only [mul_one] at h
    apply (tendsto_congr (fun n=>?_)).mpr h
    dsimp [k]
    push_cast
    field_simp
    ring
  have hd:Tendsto (fun n:ℕ=>(n+3:ℝ)/k n) atTop (𝓝 (1/2:ℝ)):=by
    have h:=(jacobi.Reference.shifted_nat_ratio 3 2).const_mul (1/2:ℝ)
    simp only [mul_one] at h
    apply (tendsto_congr (fun n=>?_)).mpr h
    dsimp [k]
    push_cast
    field_simp
    ring
  have hs:Tendsto (fun n:ℕ=>4*L n*((n+1:ℝ)/k n)^3+(n+3:ℝ)/k n*(k n)⁻¹^2)
      atTop (𝓝 (1/15:ℝ)):=by
    have h:=((hL.const_mul 4).mul (hm.pow 3)).add (hd.mul (hi.pow 2))
    norm_num at h
    simpa only [inv_pow] using h
  have hlo:Tendsto (fun n:ℕ=>sqrt (4*L n*(n+1:ℝ)^3+(n+3:ℝ))/(k n)^((3:ℝ)/2))
      atTop (𝓝 (1/sqrt 15)):=by
    have h:=hs.sqrt
    rw [sqrt_div (by norm_num : (0:ℝ)≤1),sqrt_one] at h
    apply (tendsto_congr (fun n=>?_)).mpr h
    rw [gain_normalization (sqrt_nonneg _) (by dsimp [k]; positivity),
      sq_sqrt (by dsimp [L]; positivity)]
    congr 1
    have hkn:k n≠0:=by dsimp [k]; positivity
    field_simp
  have hup:=canonical_block_gain_limit.comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup
  · intro n
    have h:=(blockGainInfimum_bounds (m:=n+1) (by omega)).1
    have hn:0≤(k n)^((3:ℝ)/2):=rpow_nonneg (by dsimp [k]; positivity) _
    convert div_le_div_of_nonneg_right h hn using 1
    simp only [L,k,Nat.cast_add,Nat.cast_one]
    congr 3; ring
  · intro n
    exact div_le_div_of_nonneg_right (blockGainInfimum_bounds (m:=n+1) (by omega)).2 (by positivity)

/-- The genuine canonical block and the original Nesterov method have the printed sqrt(2) asymptotic gain ratio.
Use: completes the quantitative comparison in the source sharp gains theorem.
Article: jacobi, Theorem 5.1.
Proof: the two true gains at the same actual horizon have the positive leading constants 1/sqrt(15) and 1/sqrt(30). Their normalized ratio converges, and its exact algebraic value is sqrt(2). -/
theorem canonical_block_gain_ratio :
    Tendsto (fun m:ℕ=>unitSpectralGain (blockMethod (uniformUChain m)).realization (2*m+2)/
      unitSpectralGain (nesterovMethod 1) (2*m+2)) atTop (𝓝 (sqrt 2)) := by
  -- Divide both genuine gains by the same positive horizon power before taking their ratio.
  have hk:Tendsto (fun m:ℕ=>2*m+2) atTop atTop:=by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    omega
  have h:=canonical_block_gain_limit.div (nesterov_gain_limit.comp hk) (by positivity)
  have he:(1/sqrt 15:ℝ)/(1/sqrt 30)=sqrt 2:=by
    calc
      _=sqrt 30/sqrt 15:=by
        simp only [div_eq_mul_inv]
        simp only [one_mul,inv_inv]
        ring
      _=sqrt 2:=by rw [← sqrt_div (by norm_num : (0:ℝ)≤30)]; norm_num
  rw [he] at h
  apply (tendsto_congr (fun m=>?_)).mpr h
  have hp:(((2*m+2:ℕ):ℝ)^((3:ℝ)/2))≠0:=by positivity
  simp only [Pi.div_apply,Function.comp_apply]
  rw [div_div_div_comm,div_self hp,div_one]

end
end jacobi.Applications
