import jacobi.Applications.UniformBlockGain
import jacobi.Counterexample.UEnergyLimit

/-!
Article: jacobi, Theorem 5.1.
The genuine gain is minimized over every original U-fibre realization.
An endpoint energy bound holds for every candidate, while the uniform
chain gives the matching upper comparison.
Use: BlockComparison passes these finite inequalities to the original
sharp asymptotic optimum, with no persymmetry restriction on competitors.
-/
namespace jacobi.Applications
noncomputable section
open Set jacobi.Finite jacobi.Variational chebyshev1 chebyshev2
set_option maxHeartbeats 1000000

/-- The genuine full spectral gain is nonnegative, including the empty horizon.
Use: the full block-fibre infimum is a bounded-below ordinary real infimum.
Article: jacobi, Theorem 5.1.
Proof: its compact value set contains the nonnegative original zero-pair time norm. -/
theorem unitSpectralGain_nonneg {ι:Type*} [Fintype ι] [DecidableEq ι]
    (R:Realization ι) (k:ℕ) : 0≤unitSpectralGain R k :=
  (Real.sqrt_nonneg _).trans (unitSpectralGain_ge R k ⟨le_rfl,by norm_num⟩ ⟨le_rfl,by norm_num⟩)

/-- The ordinary infimum of the true complete spectral gains over the entire original U fibre at its original even application count.
Use: block_optimal_gain_limit proves the actual infimum claimed in the source, rather than only the canonical candidate value.
Article: jacobi, Theorem 5.1.
-/
def blockGainInfimum (m:ℕ) : ℝ :=
  sInf ((fun J:Jacobi m=>unitSpectralGain (blockMethod J).realization (2*m+2)) ''
    {J | InFiber J (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m).polynomial})

/-- Every actual block-fibre gain is nonnegative and the complete candidate set is nonempty.
Use: all ordinary-infimum comparisons in blockGainInfimum_bounds have their boundedness and nonemptiness premises discharged.
Article: jacobi, Theorem 5.1.
Proof: the genuine uniform chain belongs to the original fibre, and every true spectral gain contains a nonnegative endpoint value. -/
theorem blockGainInfimum_nonneg (m:ℕ) : 0≤blockGainInfimum m := by
  unfold blockGainInfimum
  refine le_csInf ?_ ?_
  · exact ⟨_,⟨uniformUChain m,uniformU_inFiber m,rfl⟩⟩
  · rintro y ⟨J,_,rfl⟩
    exact unitSpectralGain_nonneg _ _

/-- The genuine full-fibre block optimum is squeezed between its complete energy-infimum endpoint bound and the actual canonical block gain.
Use: BlockComparison derives the source sharp constant from the already proved full-fibre U-energy limit.
Article: jacobi, Theorem 5.1.
Proof: every actual endpoint gain squared is 4*E(J)+m+2, and the full gain dominates it. The complete normalized energy infimum bounds E(J)/m^3. The same canonical U chain belongs to the full gain fibre and supplies its upper bound. -/
theorem blockGainInfimum_bounds {m:ℕ} (hm:0<m) :
    Real.sqrt (4*(fibreEnergyInfimum (jacobi.Jacobi.nodes (1/2) (1/2)
      (by norm_num) (by norm_num) m)).toReal*(m:ℝ)^3+(m+2:ℕ))≤blockGainInfimum m ∧
    blockGainInfimum m≤unitSpectralGain (blockMethod (uniformUChain m)).realization (2*m+2) := by
  -- The lower comparison retains every original fibre member; only the upper comparison selects a canonical representative.
  let S:= jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m
  have hE:BddBelow ((fun J:Jacobi m=>J.energy/(m:ℝ)^3) '' {J | InFiber J S.polynomial}):=by
    refine ⟨0,?_⟩
    rintro y ⟨J,_,rfl⟩
    exact div_nonneg (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity)
  have hG:BddBelow ((fun J:Jacobi m=>unitSpectralGain (blockMethod J).realization (2*m+2)) ''
      {J | InFiber J S.polynomial}):=by
    refine ⟨0,?_⟩
    rintro y ⟨J,_,rfl⟩
    exact unitSpectralGain_nonneg _ _
  unfold blockGainInfimum
  constructor
  · refine le_csInf ?_ ?_
    · exact ⟨_,⟨uniformUChain m,uniformU_inFiber m,rfl⟩⟩
    rintro y ⟨J,hJ,rfl⟩
    have hEj:(fibreEnergyInfimum S).toReal*(m:ℝ)^3≤J.energy:=by
      rw [fibreEnergyInfimum_toReal]
      exact (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hm) _)).mp (csInf_le hE ⟨J,hJ,rfl⟩)
    have hep:=unitSpectralGain_ge (blockMethod J).realization (m+(m+2))
      (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
      (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
    have hs:((blockMethod J).realization.kernelNorm (m+(m+2)) 0 0)^2≤
        (unitSpectralGain (blockMethod J).realization (m+(m+2)))^2:=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (unitSpectralGain_nonneg _ _)).mpr hep
    rw [block_endpoint_square S hJ (m+2)] at hs
    rw [show m+(m+2)=2*m+2 by omega] at hs
    apply Real.sqrt_le_iff.mpr
    exact ⟨unitSpectralGain_nonneg _ _,(by change 4*(fibreEnergyInfimum S).toReal*(m:ℝ)^3+_≤_; nlinarith)⟩
  · exact csInf_le hG ⟨uniformUChain m,uniformU_inFiber m,rfl⟩

end
end jacobi.Applications
