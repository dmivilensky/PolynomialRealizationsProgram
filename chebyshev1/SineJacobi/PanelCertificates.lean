import chebyshev1.SineJacobi.QuadratureWitnesses

/-!
Article: chebyshev1, Theorem 5.2.
Accepted panel certificates bound the actual composite quadrature.
Use: `chebyshev1.SineJacobi.panelCertificateCheck_correct` feeds
`chebyshev1.SineJacobi.sineEnergy_decimal` (A decimal enclosure of the actual elliptic-profile
integral in Theorem 5.2).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
open LeanCert.Core chebyshev1.Numerics

/--
Root witnesses and dyadic bounds for one Simpson panel.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelAccepted_bounds`
uses this record of data and proof obligations to prove the bound `(min
c.bounds.1 c.bounds.2:ℝ)/2^64 ≤ simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∧ simpson
gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ≤ (max c.bounds.1 c.bounds.2:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
structure PanelCertificate where
  /-- The three pointwise energy witnesses for this quadrature panel. -/
  witness : PanelWitness
  /-- Proposed enclosure of the panel contribution, subsequently validated by the panel checker. -/
  bounds : IntervalWitness

/--
Supplies the typeclass `Lean.ToExpr PanelCertificate` by the displayed field
definitions/proofs. Each proof field establishes the corresponding class law.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev1, Theorem 5.2.
-/
instance : Lean.ToExpr PanelCertificate where
  toTypeExpr := Lean.mkConst ``PanelCertificate
  toExpr c := Lean.mkApp2 (Lean.mkConst ``PanelCertificate.mk)
    (Lean.toExpr c.witness) (Lean.toExpr c.bounds)

/--
Defines `panelAccepted` of type `Bool` by `panelWitnessValid N j c.witness && intervalCovers
(panelWitnessValue N j c.witness) c.bounds`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelAccepted_bounds`
rewrites with this definition to prove the bound `(min c.bounds.1
c.bounds.2:ℝ)/2^64 ≤ simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∧ simpson gradedEnergy
((j:ℝ)/N) ((j+1:ℝ)/N) ≤ (max c.bounds.1 c.bounds.2:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def panelAccepted (N j : ℕ) (c : PanelCertificate) : Bool :=
  panelWitnessValid N j c.witness && intervalCovers (panelWitnessValue N j c.witness) c.bounds

/--
Defines `panelsAccepted` by pattern matching with result type `ℕ → List PanelCertificate →
Bool`. The displayed branches determine the recursive cases and their returned values.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
rewrites with this definition to prove the bound `(lowerSum cs:ℝ)/2^64
≤ panelSum N j cs.length ∧ panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def panelsAccepted (N : ℕ) : ℕ → List PanelCertificate → Bool
  | _, [] => true
  | j, c::cs => panelAccepted N j c && panelsAccepted N (j+1) cs

/--
Composition of separately kernel-checked groups of panels.

Exact identity `panelsAccepted N j (cs++ds) = (panelsAccepted N j cs && panelsAccepted N
(j+cs.length) ds)`.

Use: `chebyshev1.SineJacobi.panelsAccepted_append_true` rewrites with this identity to
establish acceptance/decoding identity for the displayed finite data: `panelsAccepted N j
(cs++ds) = true`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem panelsAccepted_append (N j : ℕ) (cs ds : List PanelCertificate) :
    panelsAccepted N j (cs++ds) = (panelsAccepted N j cs && panelsAccepted N (j+cs.length) ds) := by
  induction cs generalizing j with
  | nil => simp [panelsAccepted]
  | cons c cs ih =>
    simp only [List.cons_append, panelsAccepted, ih, List.length_cons, Bool.and_assoc]
    rw [show j+1+cs.length = j+(cs.length+1) by omega]

/--
Acceptance/decoding identity for the displayed finite data: `panelsAccepted N j (cs++ds) =
true`.

Use:
`_private.chebyshev1.SineJacobi.EnergyDecimal.0.chebyshev1.SineJacobi.verifiedQuadrature`
uses this identity to construct witnesses satisfying `∃ cs : List
PanelCertificate, panelCertificateCheck 2048 cs = true`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.panelsAccepted_append` with the
arguments shown in the proof.
-/
theorem panelsAccepted_append_true {N j : ℕ} {cs ds : List PanelCertificate}
    (hc : panelsAccepted N j cs = true)
    (hd : panelsAccepted N (j+cs.length) ds = true) : panelsAccepted N j (cs++ds) = true := by
  rw [panelsAccepted_append, Bool.and_eq_true]
  exact ⟨hc, hd⟩

/--
Defines `lowerSum` of type `ℤ` by `(cs.map (fun c => min c.bounds.1 c.bounds.2)).sum`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
rewrites with this definition to prove the bound `(lowerSum cs:ℝ)/2^64
≤ panelSum N j cs.length ∧ panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def lowerSum (cs : List PanelCertificate) : ℤ := (cs.map (fun c => min c.bounds.1 c.bounds.2)).sum
/--
Defines `upperSum` of type `ℤ` by `(cs.map (fun c => max c.bounds.1 c.bounds.2)).sum`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
rewrites with this definition to prove the bound `(lowerSum cs:ℝ)/2^64
≤ panelSum N j cs.length ∧ panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def upperSum (cs : List PanelCertificate) : ℤ := (cs.map (fun c => max c.bounds.1 c.bounds.2)).sum

/--
The sum uses supplied integer bounds, independently of the validity checks.

Use: `chebyshev1.SineJacobi.panelCertificateCheck_correct` rewrites with this definition to
establish the stated quantitative bound `(11426921797/10^10:ℝ) < energyQuadrature N ∧
energyQuadrature N < (11426921799/10^10:ℝ)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def panelCertificateCheck (N : ℕ) (cs : List PanelCertificate) : Bool :=
  decide (cs.length = N-1) && panelsAccepted N 1 cs &&
    decide ((11426921797/10^10:ℚ) < lowerSum cs/2^64 ∧
      upperSum cs/2^64 < (11426921799/10^10:ℚ))

/--
Acceptance/decoding identity for the displayed finite data: `panelCertificateCheck N cs =
true`.

Use:
`_private.chebyshev1.SineJacobi.EnergyDecimal.0.chebyshev1.SineJacobi.verifiedQuadrature`
uses this identity to construct witnesses satisfying `∃ cs : List
PanelCertificate, panelCertificateCheck 2048 cs = true`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem panelCertificateCheck_intro {N : ℕ} {cs : List PanelCertificate}
    (hlen : cs.length = N-1) (hc : panelsAccepted N 1 cs = true)
    (hb : (11426921797/10^10:ℚ) < lowerSum cs/2^64 ∧
      upperSum cs/2^64 < (11426921799/10^10:ℚ)) : panelCertificateCheck N cs = true := by
  simp only [panelCertificateCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hlen, hc⟩, hb⟩

noncomputable section
open chebyshev1.Analysis
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `(min c.bounds.1 c.bounds.2:ℝ)/2^64 ≤ simpson gradedEnergy
((j:ℝ)/N) ((j+1:ℝ)/N) ∧ simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ≤ (max c.bounds.1
c.bounds.2:ℝ)/2^64`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
uses this bound to prove the bound `(lowerSum cs:ℝ)/2^64 ≤ panelSum N j
cs.length ∧ panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.Numerics.intervalCovers_correct`,
`chebyshev1.SineJacobi.panelWitnessValue_correct` with the arguments shown in the proof.
-/
private theorem panelAccepted_bounds {N j : ℕ} {c : PanelCertificate}
    (hj : 1 ≤ j) (hjN : j < N) (h : panelAccepted N j c = true) :
    (min c.bounds.1 c.bounds.2:ℝ)/2^64 ≤ simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∧
      simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ≤ (max c.bounds.1 c.bounds.2:ℝ)/2^64 := by
  -- Use the identities/estimates `chebyshev1.Numerics.intervalCovers_correct`,
  -- `chebyshev1.SineJacobi.panelWitnessValue_correct` with the arguments shown in the
  -- proof.
  simp only [panelAccepted, Bool.and_eq_true] at h
  have hp := intervalCovers_correct (panelWitnessValue_correct hj hjN h.1) h.2
  simp only [proposedInterval, IntervalRat.mem_def, Rat.cast_min, Rat.cast_max,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] at hp
  simpa only [Int.cast_min, Int.cast_max, min_div_div_right (by positivity : (0:ℝ) ≤ 2^64),
    max_div_div_right (by positivity : (0:ℝ) ≤ 2^64)] using hp

/--
Defines `panelSum` of type `ℝ` by `∑ i ∈ Finset.range n, simpson gradedEnergy (((j+i:ℕ):ℝ)/N)
((((j+i:ℕ):ℝ)+1)/N)`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelSum_succ`
rewrites with this definition to establish the identity `panelSum N j (n+1) = simpson
gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N)+panelSum N (j+1) n`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
private def panelSum (N j n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, simpson gradedEnergy (((j+i:ℕ):ℝ)/N) ((((j+i:ℕ):ℝ)+1)/N)

/--
Exact identity `panelSum N j (n+1) = simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N)+panelSum N
(j+1) n`.

Use:
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
rewrites with this identity to prove the bound `(lowerSum cs:ℝ)/2^64 ≤
panelSum N j cs.length ∧ panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
private theorem panelSum_succ (N j n : ℕ) :
    panelSum N j (n+1) = simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N)+panelSum N (j+1) n := by
  simp only [panelSum, Finset.sum_range_succ', Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1 <;> simp [Nat.add_comm, Nat.add_left_comm]

/--
The stated quantitative bound `(lowerSum cs:ℝ)/2^64 ≤ panelSum N j cs.length ∧ panelSum N j
cs.length ≤ (upperSum cs:ℝ)/2^64`.

Use: `chebyshev1.SineJacobi.panelCertificateCheck_correct` uses this bound to establish the
stated quantitative bound `(11426921797/10^10:ℝ) < energyQuadrature N ∧ energyQuadrature N <
(11426921799/10^10:ℝ)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion.
-/
private theorem panelsAccepted_bounds {N j : ℕ} {cs : List PanelCertificate}
    (hj : 1 ≤ j) (hjN : j+cs.length ≤ N) (h : panelsAccepted N j cs = true) :
    (lowerSum cs:ℝ)/2^64 ≤ panelSum N j cs.length ∧
      panelSum N j cs.length ≤ (upperSum cs:ℝ)/2^64 := by
  -- Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing j with
  | nil => simp [lowerSum, upperSum, panelSum]
  | cons c cs ih =>
    simp only [panelsAccepted, Bool.and_eq_true] at h
    have hp := panelAccepted_bounds hj (by simp only [List.length_cons] at hjN; omega) h.1
    have ht := ih (j := j+1) (by omega) (by simp only [List.length_cons] at hjN; omega) h.2
    simp only [lowerSum, upperSum, List.map_cons, List.sum_cons, Int.cast_add,
      List.length_cons, panelSum_succ, add_div, Int.cast_min, Int.cast_max]
    simpa only [add_div, lowerSum, upperSum] using And.intro (add_le_add hp.1 ht.1) (add_le_add hp.2 ht.2)

/--
Accepted panel certificates bound the actual composite quadrature.

The stated quantitative bound `(11426921797/10^10:ℝ) < energyQuadrature N ∧ energyQuadrature N
< (11426921799/10^10:ℝ)`.

Use: `chebyshev1.SineJacobi.sineEnergy_decimal` uses this bound to establish the stated
quantitative bound `(1.14269215:ℝ) < sineEnergy ∧ sineEnergy < (1.14269221:ℝ)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates
`_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
with the arguments shown in the proof.
-/
theorem panelCertificateCheck_correct {N : ℕ} {cs : List PanelCertificate} (hN : 1 ≤ N)
    (h : panelCertificateCheck N cs = true) :
    (11426921797/10^10:ℝ) < energyQuadrature N ∧
      energyQuadrature N < (11426921799/10^10:ℝ) := by
  -- Use the identities/estimates
  -- `_private.chebyshev1.SineJacobi.PanelCertificates.0.chebyshev1.SineJacobi.panelsAccepted_bounds`
  -- with the arguments shown in the proof.
  simp only [panelCertificateCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := panelsAccepted_bounds (j := 1) le_rfl
    (by rw [h.1.1]; omega) h.1.2
  have he : panelSum N 1 (N-1) = energyQuadrature N := by
    rw [panelSum, energyQuadrature, Finset.sum_Ico_eq_sum_range]
  rw [h.1.1, he] at hb
  have hl := (Rat.cast_lt (K := ℝ)).mpr h.2.1
  have hu := (Rat.cast_lt (K := ℝ)).mpr h.2.2
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] at hl hu
  exact ⟨hl.trans_le hb.1, hb.2.trans_lt hu⟩

end
end chebyshev1.SineJacobi
