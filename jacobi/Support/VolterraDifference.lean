import jacobi.Finite.WeightedKernelSum
import jacobi.Support.VolterraCosh

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The actual complex support wave differs from its actual positive
top-node solution by the printed quadratic-energy cosh bound.
Use: naturalWave_difference applies one common actual cosh bound to every source coordinate in the original finite Green sum.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine scaled Volterra energy increases with the length of the same original prefix.
Use: naturalWave_difference applies one common actual cosh bound to every source coordinate in the original finite Green sum.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the spectral displacement is unchanged and the positive integer growth factor increases with the index. -/
theorem volterraEnergy_mono (a b : ℝ) (n : ℕ) (y : ℂ) {j m : ℕ} (h:j≤m) :
    volterraEnergy a b n j y≤volterraEnergy a b n m y := by
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have h' : (j:ℝ)≤m := by exact_mod_cast h
  nlinarith

/-- Increasing the index and nonnegative majorant constant increases the genuine Volterra cosh majorant.
Use: naturalWave_firstDifference uses one common majorant for its already proved wave and error bounds throughout the actual prefix.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the actual scaled energy is nonnegative and monotone; the nonnegative square root and cosh on nonnegative arguments preserve this order. -/
theorem volterra_cosh_mono (a b : ℝ) (n : ℕ) (y : ℂ) {j m : ℕ} {B D : ℝ}
    (hBD:B≤D) (hD:0≤D) (hjm:j≤m) :
    cosh (sqrt (B*volterraEnergy a b n j y))≤cosh (sqrt (D*volterraEnergy a b n m y)) := by
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (sqrt_nonneg _),abs_of_nonneg (sqrt_nonneg _)]
  exact sqrt_le_sqrt (mul_le_mul hBD (volterraEnergy_mono a b n y hjm) (by unfold volterraEnergy; positivity) hD)

/-- The actual complex support wave has the full original error estimate relative to its genuine top-node solution.
Use: the original first-difference bound and oscillatory transition estimate use the same actual wave, top-node reference and scaled energy.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: insert the already proved global cosh wave bound into the genuine finite Green source sum. The actual weighted kernel grows at most linearly in the index distance. Summing that bound and multiplying by the original spectral displacement gives precisely the printed quadratic scaled energy. -/
theorem naturalWave_difference {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→∀y:ℂ,
      ‖naturalWave a b ha hb n m y-(topValue a b ha hb n m:ℂ)‖≤
        C*volterraEnergy a b n m y*((m:ℝ)+1)^gamma a*
          cosh (sqrt (B*volterraEnergy a b n m y)) := by
  -- All weights, kernels and spectral displacements below belong to the same original finite chain.
  obtain ⟨C,B,hC,hB,hbound⟩ := naturalWave_cosh ha hb
  obtain ⟨D,hD,hkernel⟩ := volterraKernel_linear ha hb
  refine ⟨D*C,B,mul_pos hD hC,hB,?_⟩
  filter_upwards [hbound,hkernel,eventually_ge_atTop (8:ℕ)] with n hn hk hlarge
  intro m hm y
  let W : ℕ→ℝ := fun j => ((j:ℝ)+1)^gamma a
  let v := fun j => naturalWave a b ha hb n j y
  let G := volterraKernel a b ha hb n m
  let L := C*cosh (sqrt (B*volterraEnergy a b n m y))
  have hw (j : ℕ) : 0<W j := rpow_pos_of_pos (by positivity) _
  have hv (j : ℕ) (hj:j<m) : ‖v j‖≤L*W j := by
    have he := volterraEnergy_mono a b n y hj.le
    have hh : cosh (sqrt (B*volterraEnergy a b n j y))≤
        cosh (sqrt (B*volterraEnergy a b n m y)) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (sqrt_nonneg _),abs_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left he hB.le)
    calc
      _ ≤ C*W j*cosh (sqrt (B*volterraEnergy a b n j y)) := hn j (by omega) y
      _ ≤ C*W j*cosh (sqrt (B*volterraEnergy a b n m y)) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hC.le (hw j).le)
      _ = _ := by ring
  have hg (j : ℕ) (hj:j<m) : 0≤G j ∧ G j*W j/W m≤D*((m-j:ℕ):ℝ) :=
    ⟨volterraKernel_nonneg ha hb (by omega) (by omega),hk m j hm hj.le⟩
  have hs := weighted_kernel_sum_bound v G W m (hw m) hD.le
    (mul_nonneg hC.le (cosh_pos _).le) (fun j _ => hw j) hg hv
  have heq := naturalWave_volterra a b ha hb n m (by omega) y
  have hd : v m-(topValue a b ha hb n m:ℂ)=
      (y-(cos (gamma a*step a b (n+1)):ℝ))*∑j∈Finset.range m,(G j:ℂ)*v j := by
    dsimp [v,G]
    linear_combination heq
  change ‖v m-(topValue a b ha hb n m:ℂ)‖≤_
  rw [hd,norm_mul]
  calc
    _ ≤ ‖y-(cos (gamma a*step a b (n+1)):ℝ)‖*(D*L*((m:ℝ)+1)^2*W m) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := by dsimp [L,W,volterraEnergy]; ring

end
end jacobi.Support
