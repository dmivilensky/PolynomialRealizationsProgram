import jacobi.Applications.NesterovSharp
import jacobi.Applications.StandardDescent

/-!
Strict full-horizon upper bounds from actual flowed block competitors.
The positive-degree Taylor majorants converge in both parities. The exact
padded energy formula supplies the singleton correction, and selecting the
actual parity proves the complete horizon bound for the block infimum.
Use: NesterovComparisons assembles the final lower/upper ratio sandwich.
Article: jacobi, Corollary 5.7.
Article role: the actual block and full-class ratios and the explicit strict deficit from two.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set chebyshev2
open jacobi.Finite jacobi.Jacobi jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The true infimum over all irreducible factor blocks, with every
singleton restart appended and the full horizon in the denominator.
Article: jacobi, Corollary 5.7.
-/
def paddedEndpointInfimum {N : ℕ} (S : Nodes N) (L : ℕ) : ℝ≥0∞ :=
  sInf ((fun J : Jacobi N => ENNReal.ofReal (paddedEndpointValue J L)) ''
    {J | InFiber J S.polynomial})

/-- The full closed-fibre minimum is bounded by the whole block class.
Article: jacobi, Corollary 5.7.
-/
theorem closedEndpoint_le_padded {N : ℕ} (S : Nodes N) (L : ℕ) :
    closedEndpointMinimum (S.padMinusOne L)≤paddedEndpointInfimum S L := by
  apply le_sInf
  rintro _ ⟨J,hJ,rfl⟩
  exact paddedEndpointMinimum_le S hJ L

/-- The literal Nesterov block-class optimum at every positive horizon.
Article: jacobi, Corollary 5.7.
-/
def nesterovBlockMinimum (a : ℝ) (ha : -1<a) (n : ℕ) : ℝ≥0∞ :=
  paddedEndpointInfimum (nodes a (((n%2:ℕ):ℝ)-1/2) ha
    (by linarith [Nat.cast_nonneg (α := ℝ) (n%2)]) (n/2)) (n/2+1+n%2)

/-- Every block competitor is one of the full three-term realizations.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_closed_le_block (a : ℝ) (ha : -1<a) (n : ℕ) :
    closedEndpointMinimum (nesterovClosedNodes a ha n)≤nesterovBlockMinimum a ha n := by
  rw [nesterovClosed_endpoint_eq]
  exact closedEndpoint_le_padded _ _

/-- The continuum Taylor value at the certified explicit descent time.
Article: jacobi, Corollary 5.7.
-/
def descentTaylorValue (a : ℝ) : ℝ :=
  standardEnergy a+descentTime a*standardSlope a+
    12*(standardMass a)^2*exp (4*standardMass a*|descentTime a|)*
      (descentTime a)^2*standardEnergy a

/-- The actual scalar majorant of the padded flowed endpoint channel.
Article: jacobi, Corollary 5.7.
-/
def paddedFlowMajorant (a : ℝ) (ha : -(1/2:ℝ)<a) (e n : ℕ) : ℝ :=
  4*standardTaylorMajorant a ((e:ℝ)-1/2) (by linarith)
    (by linarith [Nat.cast_nonneg (α := ℝ) e]) n (descentTime a)*
      (((n+1:ℕ):ℝ)/(nesterovParityDimension e (n+1):ℝ))^3+
    (1-((n+1:ℕ):ℝ)/(nesterovParityDimension e (n+1):ℝ))*
      ((nesterovParityDimension e (n+1):ℝ)⁻¹)^2

/-- Both actual parity majorants have the same full-horizon limit.
Article: jacobi, Corollary 5.7.
-/
theorem paddedFlowMajorant_limit {a : ℝ} (ha : -(1/2:ℝ)<a) (e : ℕ) :
    Tendsto (paddedFlowMajorant a ha e) atTop (𝓝 (descentTaylorValue a/2)) := by
  have hT := standardTaylorMajorant_limit ha
    (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2) (descentTime a)
  have hr := (nesterov_real_degree_ratio e).comp (tendsto_add_atTop_nat 1)
  have hN : Tendsto (fun n : ℕ => nesterovParityDimension e (n+1)) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat 1)
    intro n
    unfold nesterovParityDimension
    omega
  have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN
  have h := ((hT.const_mul 4).mul (hr.pow 3)).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul (hi.pow 2))
  convert h using 1
  · rfl
  · congr 1
    change descentTaylorValue a/2=4*descentTaylorValue a*(1/2)^3+(1-1/2)*0^2
    ring

/-- A genuine flowed standard block supplies each finite majorant.
This discharges all realization and Taylor premises for the block class.
Article: jacobi, Corollary 5.7.
-/
theorem paddedFlowMajorant_competitor {a : ℝ} (ha : -(1/2:ℝ)<a) (e n : ℕ) :
    paddedEndpointInfimum (nodes a ((e:ℝ)-1/2) (by linarith)
      (by linarith [Nat.cast_nonneg (α := ℝ) e]) (n+1)) (n+2+e)≤
      ENNReal.ofReal (paddedFlowMajorant a ha e n) := by
  let ha' : -1<a := by linarith
  let hb : -1<(e:ℝ)-1/2 := by linarith [Nat.cast_nonneg (α := ℝ) e]
  let S := nodes a ((e:ℝ)-1/2) ha' hb (n+1)
  let J := resolventFlow S (standardFiber a ((e:ℝ)-1/2) ha' hb n) (descentTime a)
  have hp := (J.val.pencils_of_contractive (S.contractive J.property)).1
  have hmin : paddedEndpointInfimum S (n+2+e)≤ENNReal.ofReal (paddedEndpointValue J.val (n+2+e)) :=
    sInf_le ⟨J.val,J.property,rfl⟩
  refine hmin.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [paddedEndpointValue_identity e n J.val hp]
  have h := mul_le_mul_of_nonneg_right
    (standardTaylorMajorant_bound ha' hb n (descentTime a))
    (show (0:ℝ)≤4*(((n+1:ℕ):ℝ)/(nesterovParityDimension e (n+1):ℝ))^3 by positivity)
  change 4*standardFlowEnergy a ((e:ℝ)-1/2) ha' hb n (descentTime a)*_+_≤_
  unfold paddedFlowMajorant
  nlinarith

/-- The actual full-horizon block optimum is eventually bounded by
the convergent parity majorant, including the true floor degree.
Article: jacobi, Corollary 5.7.
-/
theorem nesterovBlockMajorant {a : ℝ} (ha : -(1/2:ℝ)<a) :
    ∀ᶠ n : ℕ in atTop,nesterovBlockMinimum a (by linarith) n≤
      ENNReal.ofReal (paddedFlowMajorant a ha (n%2) (n/2-1)) := by
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have h := paddedFlowMajorant_competitor ha (n%2) (n/2-1)
  have he : n/2-1+1=n/2 := by omega
  have ht : n/2-1+2+n%2=n/2+1+n%2 := by omega
  rw [he,ht] at h
  exact h

/-- The whole block class satisfies the strict improved upper bound.
This is proved with actual finite competitors for both parities.
Article: jacobi, Corollary 5.7.
-/
theorem nesterov_block_descent {a : ℝ} (ha : -(1/2:ℝ)<a) :
    limsup (nesterovBlockMinimum a (by linarith)) atTop≤
      ENNReal.ofReal ((standardEnergy a-descentGap a)/2) := by
  have hm : Tendsto (fun n : ℕ => n/2-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (le_of_eq (map_div_atTop_eq_nat 2 (by omega)))
  have h := tendsto_parity_choice (fun e n => paddedFlowMajorant a ha e (n/2-1))
    (fun n => n%2) (fun _ => by omega)
    ((paddedFlowMajorant_limit ha 0).comp hm) ((paddedFlowMajorant_limit ha 1).comp hm)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hle := (limsup_le_limsup (f := atTop) (nesterovBlockMajorant ha)).trans_eq hlim.limsup_eq
  exact hle.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (descentTime_taylor_bound ha) (by norm_num)))

end
end jacobi.Applications
