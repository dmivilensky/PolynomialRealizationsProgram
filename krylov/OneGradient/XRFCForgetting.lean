import krylov.OneGradient.TrialAmplitudes
import krylov.OneGradient.XRFCBidiagonal
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, actual geometric forgetting of trial errors.
Use: bound the original measured XRFC amplitudes and compare its true
sharp direction-basis coefficient with the original FC error-profile sum.
Source: genuine chronological trial-amplitude formula, finite product
monotonicity and the actual CG Pythagorean energy-drop identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- Actual CG step energy is bounded by the true current CG error energy.
Use: compare the genuine measured trial amplitude with the original FC tail.
Article: main_krylov, prop:where.
Proof: the genuine CG energy drop is the old squared error minus the
nonnegative new squared error; take nonnegative square roots. -/
theorem cg_sqrt_energy_le_error (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Real.sqrt (cgEnergy base g k)≤‖cgCanonicalError base g k‖ := by
  rw [cgEnergy_sqrt base hb]
  have h := cgEnergy_drop base hb g k
  rw [cgEnergy_eq_norm_sq base hb] at h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖cgCanonicalError base g (k+1)‖]

/-- Every actual original XRFC trial amplitude obeys the printed geometric
forgetting estimate, with exact trials and zero factors included.
Use: earlier measured trial errors decay by the genuine later correction ratios.
Article: main_krylov, prop:where, abs(a_l)<=epsBar thetaBar^(N-1-l) sqrt(c_l).
Proof: use the already proved exact actual absolute-amplitude formula.
Each true later ratio is bounded by thetaBar, so finite product monotonicity
and the exact interval cardinality give the chronological power. -/
theorem xrfc_trial_coefficient_forgetting
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : N≤referenceAtomCount base hb g)
    (epsBar thetaBar : ℝ) (heps : 0≤epsBar)
    (hErr : ∀ j<N,|xrfcTrialError trial base g j|≤epsBar)
    (hRatio : ∀ j,1≤j → j<N →
      |(CG.length (cgOperator base) g j-
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j))/
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)|≤thetaBar)
    (l : ℕ) (hl : l<N) :
    |xrfcTrialCoefficient trial base g N l|≤epsBar*thetaBar^(N-1-l)*Real.sqrt (cgEnergy base g l) := by
  let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)
  have hp : (∏ j∈Finset.Ico (l+1) N,|(CG.length (cgOperator base) g j-tau j)/tau j|)≤thetaBar^(N-1-l) := by
    calc
      _ ≤ ∏ j∈Finset.Ico (l+1) N,thetaBar := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro j hj
        exact hRatio j (by have := (Finset.mem_Ico.mp hj).1;omega) (Finset.mem_Ico.mp hj).2
      _ = _ := by
        rw [Finset.prod_const,Nat.card_Ico]
        congr 1
        omega
  have hnonneg : 0≤∏ j∈Finset.Ico (l+1) N,|(CG.length (cgOperator base) g j-tau j)/tau j| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [xrfc_trial_coefficient_abs trial base hb g N l (hl.trans_le hN)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hErr l hl) hp hnonneg heps) (Real.sqrt_nonneg _)

/-- Under the original nonamplifying later-trial factors and decreasing
budgets, the actual sharp direction-basis constant is bounded by the printed
FC error-profile coefficient plus its explicit initial launch term.
Use: retain the true launch term instead of assuming pointwise XRFC dominance.
Article: main_krylov, prop:where, C_D<=epsBar(C_FC+thetaBar^(N-1) omega_0 sqrt(c_0)).
Proof: the actual first amplitude keeps its full chronological power. Later
powers are at most one; their true step energies are bounded by the preceding
FC tail norm, and decreasing budgets move each term to its actual preceding
FC index. Split the genuine finite sum at zero and append a nonnegative final
FC term; at full reference exhaustion that term is genuinely zero. -/
theorem xrfc_direction_constant_le_FC
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : N≤referenceAtomCount base hb g) (hn : 0<N)
    (epsBar thetaBar : ℝ) (heps : 0≤epsBar) (htheta : 0≤thetaBar) (htheta1 : thetaBar≤1)
    (hErr : ∀ j<N,|xrfcTrialError trial base g j|≤epsBar)
    (hRatio : ∀ j,1≤j → j<N →
      |(CG.length (cgOperator base) g j-
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j))/
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)|≤thetaBar)
    (omega : ℕ → ℝ) (hw : ∀ j<N,0≤omega j)
    (hmono : ∀ j,j+1<N → omega (j+1)≤omega j) :
    (∑ l∈Finset.range N,omega l*|xrfcTrialCoefficient trial base g N l|)≤
      epsBar*(thetaBar^(N-1)*omega 0*Real.sqrt (cgEnergy base g 0)+
        ∑ l∈Finset.range N,omega l*‖cgCanonicalError base g (l+1)‖) := by
  let f := fun l => omega l*|xrfcTrialCoefficient trial base g N l|
  let launch := thetaBar^(N-1)*omega 0*Real.sqrt (cgEnergy base g 0)
  have hcoeff := xrfc_trial_coefficient_forgetting trial base hb g N hN epsBar thetaBar heps hErr hRatio
  have hfirst : f 0≤epsBar*launch := by
    calc
      _ ≤ omega 0*(epsBar*thetaBar^(N-1-0)*Real.sqrt (cgEnergy base g 0)) :=
        mul_le_mul_of_nonneg_left (hcoeff 0 hn) (hw 0 hn)
      _ = _ := by dsimp only [launch];rw [Nat.sub_zero];ring
  have htail (j : ℕ) (hj : j<N-1) : f (j+1)≤epsBar*(omega j*‖cgCanonicalError base g (j+1)‖) := by
    have hjn : j+1<N := by omega
    have hamp : |xrfcTrialCoefficient trial base g N (j+1)|≤epsBar*‖cgCanonicalError base g (j+1)‖ := by
      calc
        _ ≤ epsBar*thetaBar^(N-1-(j+1))*Real.sqrt (cgEnergy base g (j+1)) := hcoeff (j+1) hjn
        _ ≤ epsBar*Real.sqrt (cgEnergy base g (j+1)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right heps (pow_le_one₀ htheta htheta1)) (Real.sqrt_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (cg_sqrt_energy_le_error base hb g (j+1)) heps
    calc
      _ ≤ omega j*(epsBar*‖cgCanonicalError base g (j+1)‖) :=
        mul_le_mul (hmono j hjn) hamp (abs_nonneg _) (hw j (by omega))
      _ = _ := by ring
  have hsplit : (∑ l∈Finset.range N,f l)=f 0+∑ j∈Finset.range (N-1),f (j+1) := by
    have h := Finset.sum_range_add f 1 (N-1)
    rw [show 1+(N-1)=N by omega] at h
    simpa only [Finset.sum_range_one,Nat.one_add] using h
  have hsum : (∑ j∈Finset.range (N-1),omega j*‖cgCanonicalError base g (j+1)‖)≤
      ∑ j∈Finset.range N,omega j*‖cgCanonicalError base g (j+1)‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N 1))
    intro j hj _
    exact mul_nonneg (hw j (Finset.mem_range.mp hj)) (norm_nonneg _)
  change (∑ l∈Finset.range N,f l)≤epsBar*(launch+_)
  rw [hsplit]
  calc
    _ ≤ epsBar*launch+∑ j∈Finset.range (N-1),epsBar*(omega j*‖cgCanonicalError base g (j+1)‖) :=
      add_le_add hfirst (Finset.sum_le_sum (fun j hj => htail j (Finset.mem_range.mp hj)))
    _ = epsBar*(launch+∑ j∈Finset.range (N-1),omega j*‖cgCanonicalError base g (j+1)‖) := by
      rw [mul_add,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) heps

end
end krylov.OneGradient
