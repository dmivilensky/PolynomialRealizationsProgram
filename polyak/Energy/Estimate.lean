import polyak.Energy.Trajectory
import polyak.Energy.Interval
import polyak.Growth.Window

/-!
Article: Appendix A, Lemma energy.
Use: every actual strict spectral certificate gives one uniform trajectory energy estimate.
Proof: nonnegative actual interpolation slacks, exact charge cancellation, finite Hilbert
Parseval, cutoff localization and the proved sampled-value boundary estimate.
-/

namespace polyak.Energy
noncomputable section
open Duality Spectral Growth

/-- Article: the two endpoint-window conventions agree exactly. Use: bridge the spectral
energy estimate and the plateau argument without changing constants or indices. -/
theorem window_eq_energyWindow (b : ℕ → ℝ) (w k : ℕ) :
    window b w k = energyWindow b w k := by
  simp only [window, energyWindow, mass, ← Finset.Ico_add_one_right_eq_Icc]

/-- Article: Lemma energy. Use: the complete strict-certificate estimate for all actual functions
and finite dimensions; every symbol and interpolation hypothesis is discharged. -/
theorem _root_.polyak.Duality.StrictCertificate.windowEnergyBound {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (hB : B ≠ 0) :
    ∃ K : ℝ, ∃ w : ℕ, 0 < K ∧ WindowEnergyBound A B β t K w := by
  let kernel := certificateKernel A B β t cert
  obtain ⟨R,hR,hsupport⟩ := exists_kernel_radius kernel (cert.lags.sup id+2)
  let w := 2*R
  have hw : ∀ n ∈ cert.lags, n ≤ w := by
    intro n hn
    have hh : n ≤ cert.lags.sup id := Finset.le_sup (f := id) hn
    dsimp [w]
    omega
  have hwpos : 1 ≤ w := by dsimp [w]; omega
  let M := kernelSize kernel + valueBoundaryConstant cert
  have hM : 0 ≤ M := add_nonneg (kernelSize_nonneg _) (valueBoundaryConstant_nonneg _)
  let K := M/cert.ε+1
  have hK : 0 < K := by
    have hh := div_nonneg hM cert.ε_pos.le
    dsimp [K]
    linarith
  refine ⟨K,w,hK,fun d r i j hi hij => ?_⟩
  let f := discountedPosition r.x t
  let σ := discountedPosition (fun k => gradient r.ψ (r.x k)) t
  let h := discountedValue (fun k => r.ψ (r.x k)) t
  let b := discountedEnergy r.x t
  have hb : ∀ k, 0 ≤ b k := discountedEnergy_nonneg r.x t
  have hf : (fun k => ‖f k‖^2)=b := funext (norm_discountedPosition_sq r.x t)
  have hquad := sum_kernelEval_nat_interval_le kernel f
    (certificateKernel_symbol_le A B β t hB cert) R hsupport i j hi hij
  have heq : (∑ k ∈ Finset.Icc i j, kernelEval kernel (fun l => f l.toNat) k) =
      ∑ k ∈ Finset.Icc i j, certificateQuadratic cert f σ k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact r.kernelEval_eq_certificateQuadratic cert hB k
      (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [heq, hf] at hquad
  have hvalues := abs_sum_certificateValue_le cert hb hij hw
    (fun l _ => r.abs_discountedValue_le t l)
  change |∑ k ∈ Finset.Icc i j, certificateValue cert h k| ≤
    valueBoundaryConstant cert*(window b w i+window b w j) at hvalues
  have hslacks : 0 ≤ ∑ k ∈ Finset.Icc i j, certificateSlack cert f σ h k :=
    Finset.sum_nonneg (fun k _ => r.certificateSlack_nonneg cert k)
  simp_rw [certificateSlack_eq] at hslacks
  rw [Finset.sum_add_distrib] at hslacks
  have hvalup := (le_abs_self (∑ k ∈ Finset.Icc i j, certificateValue cert h k)).trans hvalues
  have hnorm : cert.ε*(∑ k ∈ Finset.Icc i j, b k) ≤ M*(window b w i+window b w j) := by
    change (∑ k ∈ Finset.Icc i j, certificateQuadratic cert f σ k) ≤
      -cert.ε*(∑ k ∈ Finset.Icc i j,b k)+kernelSize kernel*(window b w i+window b w j) at hquad
    dsimp [M]
    linarith
  have hwin : 0 ≤ window b w i+window b w j := add_nonneg (window_nonneg hb _ _) (window_nonneg hb _ _)
  have hdiv : (∑ k ∈ Finset.Icc i j,b k) ≤ (M/cert.ε)*(window b w i+window b w j) := by
    calc
      _ ≤ (M*(window b w i+window b w j))/cert.ε :=
        (le_div_iff₀ cert.ε_pos).mpr (by nlinarith)
      _ = _ := by ring
  have hfinal : (∑ k ∈ Finset.Icc i j,b k) ≤ K*(window b w i+window b w j) := by
    dsimp [K]
    nlinarith
  simpa only [mass, Finset.Ico_add_one_right_eq_Icc, ← window_eq_energyWindow] using hfinal

end
end polyak.Energy
