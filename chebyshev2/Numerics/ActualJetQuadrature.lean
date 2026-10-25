import chebyshev2.Numerics.ActualJetCover
import chebyshev2.Numerics.QuadratureBest
import chebyshev2.Certificates.Partition

/-!
Article: chebyshev2, Lemma 20.
`chebyshev2.Numerics.actualJetIntegralBox_sound_on` sums complete panel enclosures for the
actual function on its actual domain.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.quadrature_taylor_even`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set MeasureTheory chebyshev2.Certificates LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `ActualJetCell.integralBox` of type `IntervalRat` by `quadratureBestEnclosure c.jet
c.jet ((c.domain.hi-c.domain.lo)/2) n`.

Use: `chebyshev2.Numerics.ActualJetCell.integral_enclosed` uses this definition to
establish membership in the specified domain/enclosure: `(∫ t in (c.domain.lo:ℝ)..c.domain.hi,f
t)∈c.integralBox`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def ActualJetCell.integralBox {f : ℝ → ℝ} {n : ℕ} (c : ActualJetCell f (n+1)) : IntervalRat :=
  quadratureBestEnclosure c.jet c.jet ((c.domain.hi-c.domain.lo)/2) n

/--
Membership in the specified domain/enclosure: `(∫ t in (c.domain.lo:ℝ)..c.domain.hi,f
t)∈c.integralBox`.

Use: `chebyshev2.Numerics.actualJetIntegralBox_sound` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.quadratureBestEnclosure_sound`
with the arguments shown in the proof.
-/
theorem ActualJetCell.integral_enclosed {f : ℝ → ℝ} {n : ℕ} (c : ActualJetCell f (n+1))
    (hc : c.domain.lo<c.domain.hi)
    (hf : ContDiffOn ℝ (n+1) f (Icc (c.domain.lo:ℝ) c.domain.hi)) :
    (∫ t in (c.domain.lo:ℝ)..c.domain.hi,f t)∈c.integralBox := by
  -- Use the identities/estimates `chebyshev2.Numerics.quadratureBestEnclosure_sound` with
  -- the arguments shown in the proof.
  let m : ℝ := ((c.domain.lo:ℝ)+c.domain.hi)/2
  let h : ℚ := (c.domain.hi-c.domain.lo)/2
  have hh : 0≤h := by dsimp [h]; linarith
  have hl : m-(h:ℝ)=(c.domain.lo:ℝ) := by dsimp [m,h]; push_cast; ring
  have hr : m+(h:ℝ)=(c.domain.hi:ℝ) := by dsimp [m,h]; push_cast; ring
  have hm : m∈Icc (c.domain.lo:ℝ) c.domain.hi := by
    have hle : (c.domain.lo:ℝ)<c.domain.hi := by exact_mod_cast hc
    dsimp [m]
    constructor <;> linarith
  have hquad := quadratureBestEnclosure_sound (point := c.jet) (whole := c.jet) hh
    (c := m) (by simpa only [hl,hr] using hf)
    (by simpa only [hl,hr] using c.actual m hm)
    (by simpa only [hl,hr] using c.actual)
  simpa only [hl,hr,ActualJetCell.integralBox,h] using hquad

/--
Defines `actualJetIntegralBox` by pattern matching with result type `List (ActualJetCell f
(n+1)) → IntervalRat`. The displayed branches determine the recursive cases and their returned
values.

Use: `chebyshev2.Numerics.actualJetIntegralBox_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def actualJetIntegralBox {f : ℝ → ℝ} {n : ℕ} : List (ActualJetCell f (n+1)) → IntervalRat
  | [] => IntervalRat.singleton 0
  | c::cs => IntervalRat.add c.integralBox (actualJetIntegralBox cs)

/--
The precise assertion is `IntervalIntegrable f volume (a:ℝ) b`.

Use: `chebyshev2.Numerics.actualJetIntegralBox_sound` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `cells` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem actualJetCover_intervalIntegrable {f : ℝ → ℝ} {n : ℕ}
    (cells : List (ActualJetCell f (n+1))) {a b : ℚ}
    (hp : PartitionFrom a b (cells.map ActualJetCell.domain))
    (hf : ∀ c∈cells,ContDiffOn ℝ (n+1) f (Icc (c.domain.lo:ℝ) c.domain.hi)) :
    IntervalIntegrable f volume (a:ℝ) b := by
  -- Induct on `cells` while keeping `a` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cells generalizing a with
  | nil =>
    change a=b at hp
    subst b
    simp
  | cons c cs ih =>
    rcases hp with ⟨hlo,hlt,htail⟩
    have hfirst : IntervalIntegrable f volume (c.domain.lo:ℝ) c.domain.hi := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (by exact_mod_cast hlt.le : (c.domain.lo:ℝ)≤c.domain.hi)] using
        (hf c List.mem_cons_self).continuousOn
    have hrest := ih htail (fun d hd => hf d (List.mem_cons_of_mem c hd))
    rw [← hlo]
    exact hfirst.trans hrest

/--
Membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Use: `chebyshev2.Numerics.actualJetIntegralBox_sound_on` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `cells` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem actualJetIntegralBox_sound {f : ℝ → ℝ} {n : ℕ}
    (cells : List (ActualJetCell f (n+1))) {a b : ℚ}
    (hp : PartitionFrom a b (cells.map ActualJetCell.domain))
    (hf : ∀ c∈cells,ContDiffOn ℝ (n+1) f (Icc (c.domain.lo:ℝ) c.domain.hi)) :
    (∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox cells := by
  -- Induct on `cells` while keeping `a` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cells generalizing a with
  | nil =>
    change a=b at hp
    subst b
    simpa only [actualJetIntegralBox,intervalIntegral.integral_same,Rat.cast_zero] using
      IntervalRat.mem_singleton (0:ℚ)
  | cons c cs ih =>
    rcases hp with ⟨hlo,hlt,htail⟩
    have hfirst := c.integral_enclosed hlt (hf c List.mem_cons_self)
    have hrest := ih htail (fun d hd => hf d (List.mem_cons_of_mem c hd))
    have hInt := actualJetCover_intervalIntegrable [c]
      (show PartitionFrom c.domain.lo c.domain.hi ([c].map ActualJetCell.domain) from
        ⟨rfl,hlt,rfl⟩) (by simpa using hf c List.mem_cons_self)
    have htailInt := actualJetCover_intervalIntegrable cs htail
      (fun d hd => hf d (List.mem_cons_of_mem c hd))
    rw [← hlo,← intervalIntegral.integral_add_adjacent_intervals hInt htailInt]
    exact IntervalRat.mem_add hfirst hrest

/--
Membership in the specified domain/enclosure: `(∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox
cells`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.calibration_constant_enclosed` uses this
assertion to establish membership in the specified domain/enclosure: `(R.calibration (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma) hb ho).J 2∈IntervalRat.sub H T`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.actualJetIntegralBox_sound`,
`chebyshev2.Certificates.PartitionFrom.bounds` with the arguments shown in the proof.
-/
theorem actualJetIntegralBox_sound_on {f : ℝ → ℝ} {n : ℕ}
    (cells : List (ActualJetCell f (n+1))) {a b : ℚ}
    (hp : PartitionFrom a b (cells.map ActualJetCell.domain))
    (hf : ContDiffOn ℝ (n+1) f (Icc (a:ℝ) b)) :
    (∫ t in (a:ℝ)..b,f t)∈actualJetIntegralBox cells := by
  -- Use the identities/estimates `chebyshev2.Numerics.actualJetIntegralBox_sound`,
  -- `chebyshev2.Certificates.PartitionFrom.bounds` with the arguments shown in the proof.
  apply actualJetIntegralBox_sound cells hp
  intro c hc
  have hb := hp.bounds c.domain (List.mem_map.mpr ⟨c,hc,rfl⟩)
  exact hf.mono (Icc_subset_Icc (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.2))

end chebyshev2.Numerics
