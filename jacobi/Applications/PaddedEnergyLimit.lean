import jacobi.Finite.PaddedBlocks
import jacobi.Applications.AllThreeTerm

/-!
Full-horizon normalization of the genuine restarted block energy.
The exact energy splitting is combined with the actual degree/horizon
ratio and the vanishing singleton correction. Use: NesterovComparisons
inserts the canonical symmetric candidates and the flowed standard ones.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
Article role: genuine padded block competitors and their full-horizon endpoint normalization.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set chebyshev2
open jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The normalized squared endpoint channel of an actual padded block.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
def paddedEndpointValue {N : ℕ} (J : Jacobi N) (L : ℕ) : ℝ :=
  4*(appendMinusOne J L).energy/((N+L:ℕ):ℝ)^3

/-- Any genuine factor competitor bounds the full closed-fibre minimum.
All normalizations use the full padded degree.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem paddedEndpointMinimum_le {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) (L : ℕ) :
    closedEndpointMinimum (S.padMinusOne L)≤ENNReal.ofReal (paddedEndpointValue J L) := by
  have h : closedFibreEnergyInfimum (S.padMinusOne L)≤fibreCost (appendMinusOne J L) :=
    sInf_le ⟨_,S.appendMinusOne_mem hJ L,rfl⟩
  have hh := mul_le_mul_of_nonneg_left h (show (0:ℝ≥0∞)≤4 from bot_le)
  refine hh.trans_eq ?_
  unfold fibreCost paddedEndpointValue
  calc
    (4:ℝ≥0∞)*ENNReal.ofReal ((appendMinusOne J L).energy/((N+L:ℕ):ℝ)^3)=
        ENNReal.ofReal (4*((appendMinusOne J L).energy/((N+L:ℕ):ℝ)^3)) := by
      simpa only [ENNReal.ofReal_ofNat] using
        (ENNReal.ofReal_mul (q := (appendMinusOne J L).energy/((N+L:ℕ):ℝ)^3)
          (by norm_num : (0:ℝ)≤4)).symm
    _=_ := by congr 1; ring

/-- The exact padded channel formula in terms of the factor's own
normalized energy, the degree ratio and the singleton correction.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem paddedEndpointValue_identity (e n : ℕ) (J : Jacobi (n+1))
    (hp : (1-J.matrix).PosDef) :
    paddedEndpointValue J (n+2+e)=
      4*(J.energy/((n+1:ℕ):ℝ)^3)*
        (((n+1:ℕ):ℝ)/(nesterovParityDimension e (n+1):ℝ))^3+
      (1-((n+1:ℕ):ℝ)/(nesterovParityDimension e (n+1):ℝ))*
        ((nesterovParityDimension e (n+1):ℝ)⁻¹)^2 := by
  rw [paddedEndpointValue,appendMinusOne_energy J hp]
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  have hN : (nesterovParityDimension e (n+1):ℝ)≠0 := Nat.cast_ne_zero.mpr (by
    unfold nesterovParityDimension
    omega)
  dsimp only [nesterovParityDimension] at hN ⊢
  push_cast at hN ⊢
  field_simp
  ring

/-- Genuine block sequences with factor energy C have full-horizon
endpoint constant C/2. This includes the exact vanishing restart cost.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem paddedEndpointValue_limit (e : ℕ) (J : ∀ n,Jacobi (n+1))
    (hp : ∀ n,(1-(J n).matrix).PosDef) {C : ℝ}
    (hE : Tendsto (fun n : ℕ => (J n).energy/((n+1:ℕ):ℝ)^3) atTop (𝓝 C)) :
    Tendsto (fun n : ℕ => paddedEndpointValue (J n) (n+2+e)) atTop (𝓝 (C/2)) := by
  have hr := (nesterov_real_degree_ratio e).comp (tendsto_add_atTop_nat 1)
  have hN : Tendsto (fun n : ℕ => nesterovParityDimension e (n+1)) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat 1)
    intro n
    unfold nesterovParityDimension
    omega
  have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN
  have h := ((hE.const_mul 4).mul (hr.pow 3)).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul (hi.pow 2))
  have he : 4*C*(1/2:ℝ)^3+(1-1/2)*0^2=C/2 := by ring
  rw [he] at h
  convert h using 1
  funext n
  rw [paddedEndpointValue_identity e n _ (hp n)]
  rfl

/-- Exact dimension transports leave the finite endpoint minimum unchanged.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem castClosedNodes_endpoint {N M : ℕ} (h : N=M) (S : ClosedNodes N) :
    closedEndpointMinimum (castClosedNodes h S)=closedEndpointMinimum S := by
  subst M
  rfl

/-- The full-horizon optimum equals its literal parity-fibre optimum.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem nesterovClosed_endpoint_eq (a : ℝ) (ha : -1<a) (n : ℕ) :
    closedEndpointMinimum (nesterovClosedNodes a ha n)=
      closedEndpointMinimum (nesterovParityNodes a ha (n%2) (n/2)) :=
  castClosedNodes_endpoint _ _

/-- Convergent concrete upper competitors for both positive-degree
parities give the complete full-horizon upper bound. Only finitely many
zero-degree horizons are discarded, and no parity limit is assumed.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem nesterovClosed_upper_of_competitors {a C : ℝ} (ha : -1<a)
    (R : ℕ → ℕ → ℝ)
    (h0 : Tendsto (R 0) atTop (𝓝 C)) (h1 : Tendsto (R 1) atTop (𝓝 C))
    (hR : ∀ e : ℕ,e≤1 → ∀ n : ℕ,
      closedEndpointMinimum (nesterovParityNodes a ha e (n+1))≤ENNReal.ofReal (R e n)) :
    limsup (fun n : ℕ => closedEndpointMinimum (nesterovClosedNodes a ha n)) atTop≤
      ENNReal.ofReal C := by
  have hm : Tendsto (fun n : ℕ => n/2-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (le_of_eq (map_div_atTop_eq_nat 2 (by omega)))
  have h := tendsto_parity_choice (fun e n => R e (n/2-1)) (fun n => n%2)
    (fun _ => by omega) (h0.comp hm) (h1.comp hm)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hb : ∀ᶠ n : ℕ in atTop,closedEndpointMinimum (nesterovClosedNodes a ha n)≤
      ENNReal.ofReal (R (n%2) (n/2-1)) := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    rw [nesterovClosed_endpoint_eq]
    have he : n/2-1+1=n/2 := by omega
    have hr := hR (n%2) (by omega) (n/2-1)
    rw [he] at hr
    exact hr
  exact (limsup_le_limsup (f := atTop) hb).trans_eq hlim.limsup_eq

end
end jacobi.Applications
