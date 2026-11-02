import krylov.OneGradient.LaggedSmooth
import krylov.OneGradient.TrialForgetting
import krylov.Reference.EnergyPositive
import krylov.OneGradient.XRFCBidiagonal
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb(b), actual growing-reference lagged analysis.
Use: transfer uniform chronological forgetting to genuine full-atom matrix
references, their actual observed errors, amplitudes and sharp direction sum.
Source: original measured lagged dictionary and the proved uniform product limit.
-/

namespace krylov.OneGradient
noncomputable section
open Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Envelope
open scoped BigOperators InnerProductSpace

/-- The single chronological trial sequence forced by actual lagged
measurements on every prefix of a common positive CG-length sequence.
Use: retain the arbitrary original positive initialization.
Article: main_krylov, prop:hb(b). -/
def laggedSequenceTrial (tau0 : ℝ) (alpha : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k=0 then tau0 else alpha (k-1)

/-- Actual measured lagged decisions on every real quadratic prefix equal
the common lagged sequence dictated by its true CG lengths.
Use: the scalar sequence is a proved implementation dictionary.
Article: main_krylov, prop:hb(b).
Proof: the empty actual cache returns tau0; the next actual decision is the
previous observed CG line length in either original source basis. -/
theorem lagged_trial_sequence {n : ℕ} (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (alpha : ℕ → ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha i)
    (k : ℕ) (hk : k<n) :
    let trial := laggedTrial directions tau0
    trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)=
      laggedSequenceTrial tau0 alpha k := by
  cases k with
  | zero => rfl
  | succ k =>
    have hp := cgOperator_positive base hb
    have h := lagged_trial_step_reference_next directions htau0 (cgOperator base) hp.1 hp.2 g n
      (fun i hi => cg_nonstagnation base hb g i (by omega)) k (by omega)
    exact h.trans (halpha k (by omega))

/-- A common positive limiting CG length makes the actual lagged relative
trial defect and the actual correction multiplier tend to zero.
Use: both scalar hypotheses of uniform full-horizon forgetting are derived.
Article: main_krylov, prop:hb(b).
Proof: shifting the convergent length sequence preserves its positive limit;
division is continuous there and the finite initialization does not affect it. -/
theorem lagged_sequence_limits (tau0 : ℝ) (alpha : ℕ → ℝ) (limit : ℝ)
    (hlimit : 0<limit) (halpha : Tendsto alpha atTop (𝓝 limit)) :
    Tendsto (fun k => 1-laggedSequenceTrial tau0 alpha k/alpha k) atTop (𝓝 0) ∧
      Tendsto (fun k => (alpha k-laggedSequenceTrial tau0 alpha k)/laggedSequenceTrial tau0 alpha k)
        atTop (𝓝 0) := by
  have ht : Tendsto (laggedSequenceTrial tau0 alpha) atTop (𝓝 limit) := by
    apply (halpha.comp (tendsto_sub_atTop_nat 1)).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
    exact (ite_eq_right (show k≠0 by omega)).symm
  constructor
  · have h := (tendsto_const_nhds (x := (1:ℝ))).sub (ht.div halpha hlimit.ne')
    change Tendsto (fun k => 1-laggedSequenceTrial tau0 alpha k/alpha k) atTop (𝓝 (1-limit/limit)) at h
    simpa only [div_self hlimit.ne',sub_self] using h
  · have h := (halpha.sub ht).div ht hlimit.ne'
    change Tendsto (fun k => (alpha k-laggedSequenceTrial tau0 alpha k)/laggedSequenceTrial tau0 alpha k)
      atTop (𝓝 ((limit-limit)/limit)) at h
    simpa only [sub_self,zero_div] using h

/-- The actual normalized full-horizon lagged amplitudes on a real matrix
reference are exactly the original chronological defect products.
Use: transfer uniform forgetting to genuine measured physical energies.
Article: main_krylov, prop:hb(b).
Proof: insert the original actual amplitude identity and replace each true
observed trial and true CG length by its proved common-prefix dictionary. -/
theorem lagged_coefficient_sequence {n : ℕ} (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (alpha : ℕ → ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha i)
    (l : ℕ) (hl : l<n) :
    |xrfcTrialCoefficient (laggedTrial directions tau0) base g n l|=
      (|1-laggedSequenceTrial tau0 alpha l/alpha l| *
        (∏ i∈Finset.Ico (l+1) n,|(alpha i-laggedSequenceTrial tau0 alpha i)/
          laggedSequenceTrial tau0 alpha i|))*Real.sqrt (cgEnergy base g l) := by
  let trial : History (EuclideanSpace ℝ (Fin n)) → ℝ := laggedTrial directions tau0
  let tau := fun i => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)
  have ht (i : ℕ) (hi : i<n) : tau i=laggedSequenceTrial tau0 alpha i :=
    lagged_trial_sequence directions htau0 base hb g hc alpha halpha i hi
  rw [xrfc_trial_coefficient_abs trial base hb g n l (by omega)]
  dsimp only
  change |1-tau l/CG.length (cgOperator base) g l| *
      (∏ i∈Finset.Ico (l+1) n,|(CG.length (cgOperator base) g i-tau i)/tau i|)*_= _
  rw [ht l hl,halpha l hl]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  have hin := (Finset.mem_Ico.mp hi).2
  rw [ht i hin,halpha i hin]

/-- The maximum of all real normalized lagged amplitudes tends to zero
for genuine growing full-atom references with one common limiting CG-length
sequence. The bound is simultaneous in every chronological index.
Use: this is the original source uniform maximum, with actual implementation
and strictly positive actual energy denominators.
Article: main_krylov, prop:hb(b).
Proof: uniform scalar forgetting transfers through the proved real reference
dictionary; genuine active CG energies justify cancellation of their roots. -/
theorem lagged_family_amplitudes (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : ∀ n : ℕ,Matrix (Fin n) (Fin n) ℝ) (hb : ∀ n,(base n).PosDef)
    (g : ∀ n : ℕ,EuclideanSpace ℝ (Fin n))
    (hc : ∀ n,referenceAtomCount (base n) (hb n) (g n)=n)
    (alpha : ℕ → ℝ) (halpha : ∀ n i,i<n → CG.length (cgOperator (base n)) (g n) i=alpha i)
    (limit : ℝ) (hlimit : 0<limit) (hconv : Tendsto alpha atTop (𝓝 limit))
    (delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ n in atTop,∀ l<n,
      |xrfcTrialCoefficient (laggedTrial directions tau0) (base n) (g n) n l|/
        Real.sqrt (cgEnergy (base n) (g n) l)<delta := by
  have hlim := lagged_sequence_limits tau0 alpha limit hlimit hconv
  filter_upwards [trial_products_uniform_small _ _ hlim.1 hlim.2 delta hdelta] with n hn
  intro l hl
  rw [lagged_coefficient_sequence directions htau0 (base n) (hb n) (g n) (hc n) alpha (halpha n) l hl]
  have hs : Real.sqrt (cgEnergy (base n) (g n) l)≠0 :=
    (Real.sqrt_pos.mpr (cgEnergy_pos (base n) (hb n) (g n) l (by rw [hc];exact hl))).ne'
  rw [mul_div_cancel_right₀ _ hs]
  exact hn l hl

/-- The actual measured relative trial errors on growing genuine references
form a sequence tending to zero at every selected chronological prefix index.
Use: the source epsilon limit refers to the executed data-only policy.
Article: main_krylov, prop:hb(b).
Proof: every actual finite-prefix error is the same proved common-sequence
error; its positive-limit quotient has already been shown to vanish. -/
theorem lagged_family_trial_errors (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : ∀ n : ℕ,Matrix (Fin n) (Fin n) ℝ) (hb : ∀ n,(base n).PosDef)
    (g : ∀ n : ℕ,EuclideanSpace ℝ (Fin n))
    (hc : ∀ n,referenceAtomCount (base n) (hb n) (g n)=n)
    (alpha : ℕ → ℝ) (halpha : ∀ n i,i<n → CG.length (cgOperator (base n)) (g n) i=alpha i)
    (limit : ℝ) (hlimit : 0<limit) (hconv : Tendsto alpha atTop (𝓝 limit)) :
    Tendsto (fun k => xrfcTrialError (laggedTrial directions tau0) (base (k+1)) (g (k+1)) k)
      atTop (𝓝 0) := by
  apply (lagged_sequence_limits tau0 alpha limit hlimit hconv).1.congr'
  apply Eventually.of_forall
  intro k
  change 1-laggedSequenceTrial tau0 alpha k/alpha k=
    1-laggedTrial directions tau0 (oneGradientRun (xrfcMethod fullMemory (laggedTrial directions tau0))
      (fun _ => cgOperator (base (k+1))) (g (k+1)) k)/CG.length (cgOperator (base (k+1))) (g (k+1)) k
  rw [lagged_trial_sequence directions htau0 (base (k+1)) (hb (k+1)) (g (k+1)) (hc (k+1))
    alpha (halpha (k+1)) k (by omega),halpha (k+1) k (by omega)]

/-- The original actual sharp XRFC-D budget sum is little-o of the genuine
weighted CG-energy scale, uniformly for arbitrary nonnegative growing budgets.
Use: completes the full growing-reference consequence, including zero budgets.
Article: main_krylov, prop:hb(b), C_D=o(1) sum omega_l sqrt(c_l).
Proof: the real uniform normalized-amplitude bound multiplies every true
nonnegative budget; sum it and use the defining little-o quantifier. -/
theorem lagged_family_direction_littleO (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : ∀ n : ℕ,Matrix (Fin n) (Fin n) ℝ) (hb : ∀ n,(base n).PosDef)
    (g : ∀ n : ℕ,EuclideanSpace ℝ (Fin n))
    (hc : ∀ n,referenceAtomCount (base n) (hb n) (g n)=n)
    (alpha : ℕ → ℝ) (halpha : ∀ n i,i<n → CG.length (cgOperator (base n)) (g n) i=alpha i)
    (limit : ℝ) (hlimit : 0<limit) (hconv : Tendsto alpha atTop (𝓝 limit))
    (omega : ℕ → ℕ → ℝ) (homega : ∀ n l,0≤omega n l) :
    (fun n => ∑ l∈Finset.range n,omega n l *
      |xrfcTrialCoefficient (laggedTrial directions tau0) (base n) (g n) n l|) =o[atTop]
        (fun n => ∑ l∈Finset.range n,omega n l*Real.sqrt (cgEnergy (base n) (g n) l)) := by
  rw [isLittleO_iff]
  intro delta hdelta
  filter_upwards [lagged_family_amplitudes directions htau0 base hb g hc alpha halpha
    limit hlimit hconv delta hdelta] with n hn
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun l _ =>
    mul_nonneg (homega n l) (abs_nonneg _))),abs_of_nonneg (Finset.sum_nonneg (fun l _ =>
      mul_nonneg (homega n l) (Real.sqrt_nonneg _))),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hln := Finset.mem_range.mp hl
  have hs := Real.sqrt_pos.mpr (cgEnergy_pos (base n) (hb n) (g n) l (by rw [hc];exact hln))
  have h := (div_lt_iff₀ hs).mp (hn l hln)
  calc
    _ ≤ omega n l*(delta*Real.sqrt (cgEnergy (base n) (g n) l)) :=
      mul_le_mul_of_nonneg_left h.le (homega n l)
    _ = _ := by ring

end
end krylov.OneGradient
