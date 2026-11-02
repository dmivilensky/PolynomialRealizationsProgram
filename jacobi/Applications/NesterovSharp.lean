import jacobi.Applications.PaddedEnergyLimit
import jacobi.Comparison.MainBounds

/-!
Sharpness among every three-term realization at the symmetric parameter.
The full closed-fibre lower bound is matched by actual canonical
persymmetric blocks in both parities. Their full endpoint energies tend
to one fifteenth, so the complete finite minima have that same limit.
Use: NesterovComparisons gives the exact ratio two to the original method.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
Article role: the sharp symmetric minimum and canonical attaining blocks in both parities.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set jacobi.Jacobi jacobi.Finite jacobi.Variational
open jacobi.Comparison jacobi.GelfandLevitan
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The Young calibration is also a lower bound for the three retained
homogeneous branches. No root-mass branch is needed for this comparison.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem young_le_homogeneous (Λ : EdgeSpectrum) :
    ENNReal.ofReal (jacobi.Young.youngValue Λ.second)≤homogeneousLowerConstant Λ := by
  have he : relaxedInfimum {Observation.second} Λ.mass (threshold Λ)=
      relaxedInfimum {Observation.second} Λ.mass (fun _ => Λ.second) := by
    unfold relaxedInfimum
    congr 1
    ext m
    simp only [mem_singleton_iff,forall_eq,threshold]
  exact (jacobi.Elliptic.second_infimum_young_lower Λ.second_pos.le).trans
    (by rw [← he]; exact (le_max_left _ _).trans (le_max_left _ _))

/-- The exact retained lower constant at U is two fifteenths. The upper
comparison uses the already proved full lower constant at the same spectrum.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem homogeneousLowerConstant_U :
    homogeneousLowerConstant (jacobi.Bessel.edgeSpectrum (1/2) (by norm_num))=
      ENNReal.ofReal (2/15) := by
  apply le_antisymm
  · exact (homogeneousLowerConstant_le _).trans_eq
      (jacobiOptimalEnergy_U (b := 0) (by norm_num) (by norm_num)).1
  · have h := young_le_homogeneous (jacobi.Bessel.edgeSpectrum (1/2) (by norm_num))
    rw [jacobi.Bessel.edgeSpectrum_second,show (1/(4*((1/2:ℝ)+1)^2*(1/2+2)))=2/45 by norm_num,
      jacobi.Young.youngValue_at_U] at h
    exact h

/-- The actual canonical persymmetric blocks attain the sharp full-horizon
constant in either parity, with all appended singleton costs included.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem nesterov_canonical_block_limit (e : ℕ) :
    Tendsto (fun n : ℕ => paddedEndpointValue
      (targetChain (1/2) ((e:ℝ)-1/2) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) e]) n)
      (n+2+e)) atTop (𝓝 (1/15:ℝ)) := by
  let hb : -1<(e:ℝ)-1/2 := by linarith [Nat.cast_nonneg (α := ℝ) e]
  have hp n : (1-(targetChain (1/2) ((e:ℝ)-1/2) (by norm_num) hb n).matrix).PosDef :=
    ((targetChain _ _ (by norm_num) hb n).pencils_of_contractive
      ((nodes _ _ (by norm_num) hb (n+1)).contractive
        (targetChain_inFiber _ _ (by norm_num) hb n))).1
  have hE := target_energy_limit (a := (1/2:ℝ)) (by norm_num) hb
  rw [half_sine_persymmetricConstant] at hE
  have h := paddedEndpointValue_limit e
    (fun n => targetChain (1/2) ((e:ℝ)-1/2) (by norm_num) hb n) hp
    (by simpa only [Nat.cast_add,Nat.cast_one] using hE)
  norm_num only [show (2/15:ℝ)/2=1/15 by norm_num] at h
  exact h

/-- The actual full closed-fibre endpoint minima have sharp limit one
fifteenth. Both parity candidates match the lower bound for all matrices,
including every possible restart and every endpoint-root placement.
Article: jacobi, Theorem 5.3 and Corollary 5.7.
-/
theorem nesterov_closed_sharp_limit :
    Tendsto (fun n : ℕ => closedEndpointMinimum
      (nesterovClosedNodes (1/2) (by norm_num) n)) atTop (𝓝 (ENNReal.ofReal (1/15))) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have h := nesterov_all_three_term_lower (b := 1) (by norm_num)
    norm_num only [show (1:ℝ)/2=1/2 by norm_num] at h
    rw [homogeneousLowerConstant_U,
      show (1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) by norm_num [ENNReal.ofReal_div_of_pos],
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)] at h
    norm_num only [show (1/2:ℝ)*(2/15)=1/15 by norm_num] at h
    exact h
  · apply nesterovClosed_upper_of_competitors (a := (1/2:ℝ)) (by norm_num)
      (fun e n => paddedEndpointValue (targetChain (1/2) ((e:ℝ)-1/2) (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) e]) n) (n+2+e))
      (nesterov_canonical_block_limit 0) (nesterov_canonical_block_limit 1)
    intro e _ n
    exact paddedEndpointMinimum_le _ (targetChain_inFiber _ _ _ _ n) _
  · exact isBoundedUnder_of ⟨⊤,fun _ => le_top⟩
  · exact isBoundedUnder_of ⟨⊥,fun _ => bot_le⟩

end
end jacobi.Applications
