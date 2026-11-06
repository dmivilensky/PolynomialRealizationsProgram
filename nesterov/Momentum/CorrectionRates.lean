import nesterov.Momentum.Correction
import nesterov.Momentum.Rates
import nesterov.Rates.RootBounds

/-!
Article: Remark two-step methods, equality of uniform rates under gradient correction.
Use: literal all-Hilbert physical correction executions and dimension-uniform
state comparisons identify their root limit with the source momentum rate.
-/

noncomputable section
namespace nesterov.Momentum.Correction
open scoped BigOperators Topology
open Set Filter

section Norms
variable {E : Type*} [NormedAddCommGroup E]

def size (p : E × E) : ℝ := Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)

theorem size_nonneg (p : E × E) : 0 ≤ size p := Real.sqrt_nonneg _
theorem size_sq (p : E × E) : size p ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 :=
  Real.sq_sqrt (by positivity)
theorem norm_fst_le_size (p : E × E) : ‖p.1‖ ≤ size p := by
  nlinarith [size_sq p, size_nonneg p, norm_nonneg p.1, sq_nonneg ‖p.2‖]
theorem norm_snd_le_size (p : E × E) : ‖p.2‖ ≤ size p := by
  nlinarith [size_sq p, size_nonneg p, norm_nonneg p.2, sq_nonneg ‖p.1‖]
theorem size_le_norm_add (p : E × E) : size p ≤ ‖p.1‖ + ‖p.2‖ := by
  nlinarith [size_sq p, size_nonneg p, norm_nonneg p.1, norm_nonneg p.2]

def queryBound (τ : ℝ) : ℝ := 1 + 2 * |τ|
def forwardBound (β τ h L : ℝ) : ℝ :=
  queryBound τ * (3 + 2 * |β| + |h| * |L| * queryBound τ)
def inverseBound (β τ h L : ℝ) : ℝ :=
  1 + |(determinant β τ)⁻¹| *
    (|1 + (1 + τ) * β| + |(1 + τ) * β| +
      (|1 + τ| + |τ|) * (1 + |1 + τ| * |h| * |L|))
def comparisonBound (β τ h L : ℝ) : ℝ := forwardBound β τ h L * inverseBound β τ h L

theorem queryBound_pos (τ : ℝ) : 0 < queryBound τ := by unfold queryBound; positivity
theorem forwardBound_pos (β τ h L : ℝ) : 0 < forwardBound β τ h L := by
  unfold forwardBound
  have hq := queryBound_pos τ
  exact mul_pos hq (by positivity)
theorem inverseBound_pos (β τ h L : ℝ) : 0 < inverseBound β τ h L := by unfold inverseBound; positivity
theorem comparisonBound_pos (β τ h L : ℝ) : 0 < comparisonBound β τ h L :=
  mul_pos (forwardBound_pos β τ h L) (inverseBound_pos β τ h L)

variable [NormedSpace ℝ E]

theorem norm_query_le (τ : ℝ) (p : E × E) :
    ‖Momentum.query τ p‖ ≤ queryBound τ * size p := by
  have hn : ‖Momentum.query τ p‖ ≤ ‖p.2‖ + |τ| * (‖p.2‖ + ‖p.1‖) := by
    unfold Momentum.query
    calc
      _ ≤ ‖p.2‖ + ‖τ • (p.2-p.1)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg τ))
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (norm_snd_le_size p) (norm_fst_le_size p)) (abs_nonneg τ)
  dsimp [queryBound]
  nlinarith [norm_snd_le_size p]

theorem size_step_le {g : E → E} {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖)
    (β τ h : ℝ) (p : E × E) :
    size (Momentum.step g β τ h p) ≤
      (2 + 2 * |β| + |h| * |L| * queryBound τ) * size p := by
  have hn : ‖(Momentum.step g β τ h p).2‖ ≤
      ‖p.2‖ + |β| * (‖p.2‖ + ‖p.1‖) + |h| * (|L| * ‖Momentum.query τ p‖) := by
    calc
      _ ≤ ‖p.2 + β • (p.2-p.1)‖ + ‖h • g (Momentum.query τ p)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs]
        apply add_le_add
        · exact (norm_add_le _ _).trans (add_le_add le_rfl (by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg β)))
        · exact mul_le_mul_of_nonneg_left (hg _) (abs_nonneg h)
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (norm_snd_le_size p) (norm_fst_le_size p)) (abs_nonneg β)
  have hq := mul_le_mul_of_nonneg_left (norm_query_le τ p)
    (mul_nonneg (abs_nonneg h) (abs_nonneg L))
  have hs := size_le_norm_add (Momentum.step g β τ h p)
  change _ ≤ ‖p.2‖ + ‖(Momentum.step g β τ h p).2‖ at hs
  nlinarith [norm_snd_le_size p]

theorem size_queryState_le {g : E → E} {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖)
    (β τ h : ℝ) (p : E × E) :
    size (queryState g β τ h p) ≤ forwardBound β τ h L * size p := by
  have hs := size_le_norm_add (queryState g β τ h p)
  have h0 := norm_query_le τ p
  have h1 := norm_query_le τ (Momentum.step g β τ h p)
  have hm := mul_le_mul_of_nonneg_left (size_step_le hg β τ h p) (queryBound_pos τ).le
  change _ ≤ ‖Momentum.query τ p‖ + ‖Momentum.query τ (Momentum.step g β τ h p)‖ at hs
  unfold forwardBound
  nlinarith

theorem size_inverseState_le {g : E → E} {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖)
    (β τ h : ℝ) (q : E × E) :
    size (inverseState g β τ h q) ≤ inverseBound β τ h L * size q := by
  let R := q.2 + ((1 + τ) * h) • g q.1
  have hR : ‖R‖ ≤ (1 + |1 + τ| * |h| * |L|) * size q := by
    have he : ‖R‖ ≤ ‖q.2‖ + |1 + τ| * |h| * (|L| * ‖q.1‖) := by
      calc
        _ ≤ ‖q.2‖ + ‖((1+τ)*h) • g q.1‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hg q.1) (by positivity))
    have hm := mul_le_mul_of_nonneg_left (norm_fst_le_size q)
      (show 0 ≤ |1+τ| * |h| * |L| by positivity)
    nlinarith [norm_snd_le_size q]
  have hfirst : ‖(inverseState g β τ h q).1‖ ≤
      |(determinant β τ)⁻¹| * (|1+(1+τ)*β| * ‖q.1‖ + |1+τ| * ‖R‖) := by
    change ‖(determinant β τ)⁻¹ • ((1+(1+τ)*β) • q.1 - (1+τ) • R)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le ((1+(1+τ)*β) • q.1) ((1+τ) • R)
  have hsecond : ‖(inverseState g β τ h q).2‖ ≤
      |(determinant β τ)⁻¹| * (|(1+τ)*β| * ‖q.1‖ + |τ| * ‖R‖) := by
    change ‖(determinant β τ)⁻¹ • (((1+τ)*β) • q.1 - τ • R)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le (((1+τ)*β) • q.1) (τ • R)
  have hfst := mul_le_mul_of_nonneg_left (norm_fst_le_size q)
    (show 0 ≤ |(determinant β τ)⁻¹| * (|1+(1+τ)*β| + |(1+τ)*β|) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ |(determinant β τ)⁻¹| * (|1+τ| + |τ|) by positivity)
  have hs := size_le_norm_add (inverseState g β τ h q)
  unfold inverseBound
  nlinarith [size_nonneg q]

theorem history_stateNorm (g : E → E) (β τ h : ℝ) (hh : h ≠ 0) (a b : E) (n : ℕ) :
    (Momentum.method β τ h hh).stateNorm (Momentum.history g β τ h a b) n =
      size (Momentum.state g β τ h a b n) := by
  change Real.sqrt (∑ j : Fin 2, ‖Momentum.history g β τ h a b (n+j)‖ ^ 2) = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero]
  rw [Momentum.history_eq_fst]
  rfl

end Norms

section HilbertBounds
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_bound {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (x : E) :
    ‖gradient f x‖ ≤ |L| * ‖x‖ := by
  have h := hf.grad_lipschitz x 0
  simpa only [hf.gradient_zero, sub_zero, abs_of_pos (hf.mu_pos.trans hf.mu_lt_L)] using h

theorem size_momentumState_le {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (β τ h : ℝ) (hh : h ≠ 0)
    (p : E × E) (n : ℕ) :
    size (Momentum.state (gradient f) β τ h p.1 p.2 n) ≤
      Rates.envelope (Momentum.method β τ h hh) μ L n * size p := by
  let r : Rates.HilbertRun (Momentum.method β τ h hh) μ L :=
    ⟨E, f, hf, Momentum.history (gradient f) β τ h p.1 p.2,
      Momentum.history_isTrajectory (gradient f) β τ h hh p.1 p.2⟩
  have he := Rates.stateNorm_le_envelope r n
  change (Momentum.method β τ h hh).stateNorm (Momentum.history (gradient f) β τ h p.1 p.2) n ≤
    _ * (Momentum.method β τ h hh).stateNorm (Momentum.history (gradient f) β τ h p.1 p.2) 0 at he
  simpa only [history_stateNorm, Momentum.state_zero] using he

theorem size_correctionState_le {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (β τ h : ℝ) (hh : h ≠ 0)
    (hδ : determinant β τ ≠ 0) (q : E × E) (n : ℕ) :
    size (state (gradient f) β τ h q.1 q.2 n) ≤
      comparisonBound β τ h L * Rates.envelope (Momentum.method β τ h hh) μ L n * size q := by
  let p := inverseState (gradient f) β τ h q
  have hg := gradient_bound hf
  have hforward := size_queryState_le hg β τ h
    (Momentum.state (gradient f) β τ h p.1 p.2 n)
  have hsource := size_momentumState_le hf β τ h hh p n
  have hinverse := size_inverseState_le hg β τ h q
  have hΓ := Rates.envelope_nonneg (Momentum.method β τ h hh) μ L n
  rw [state_from_inverse (gradient f) β τ h hδ]
  calc
    _ ≤ forwardBound β τ h L * size (Momentum.state (gradient f) β τ h p.1 p.2 n) := hforward
    _ ≤ forwardBound β τ h L * (Rates.envelope (Momentum.method β τ h hh) μ L n * size p) :=
      mul_le_mul_of_nonneg_left hsource (forwardBound_pos β τ h L).le
    _ ≤ forwardBound β τ h L * (Rates.envelope (Momentum.method β τ h hh) μ L n *
        (inverseBound β τ h L * size q)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinverse hΓ)
        (forwardBound_pos β τ h L).le
    _ = _ := by unfold comparisonBound; ring

end HilbertBounds

/-- Literal correction executions on arbitrary centered objectives and real
Hilbert spaces, with an arbitrary initial pair of actual query points. -/
structure Run (β τ h μ L : ℝ) where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℝ Carrier]
  [complete : CompleteSpace Carrier]
  f : Carrier → ℝ
  admissible : polyak.CenteredSmoothStronglyConvex μ L f
  initial : Carrier × Carrier

attribute [instance] Run.normed Run.inner Run.complete

namespace Run
variable {β τ h μ L : ℝ}
def pair (r : Run β τ h μ L) (n : ℕ) : r.Carrier × r.Carrier :=
  state (gradient r.f) β τ h r.initial.1 r.initial.2 n
def stateSize (r : Run β τ h μ L) (n : ℕ) : ℝ := size (r.pair n)

def shift (r : Run β τ h μ L) (k : ℕ) : Run β τ h μ L where
  Carrier := r.Carrier
  f := r.f
  admissible := r.admissible
  initial := r.pair k

@[simp] theorem pair_shift (r : Run β τ h μ L) (k n : ℕ) :
    (r.shift k).pair n = r.pair (k+n) :=
  (state_add (gradient r.f) β τ h r.initial.1 r.initial.2 k n).symm

@[simp] theorem stateSize_shift (r : Run β τ h μ L) (k n : ℕ) :
    (r.shift k).stateSize n = r.stateSize (k+n) := congrArg size (r.pair_shift k n)
end Run

def ratios (β τ h μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : Run β τ h μ L, r.stateSize 0 ≠ 0 ∧ x = r.stateSize n / r.stateSize 0}

def envelope (β τ h μ L : ℝ) (n : ℕ) : ℝ := sSup (insert 0 (ratios β τ h μ L n))

/-- Arbitrary free memories and arbitrary restart times give the same literal set. -/
theorem ratios_eq_restart_ratios (β τ h μ L : ℝ) (n : ℕ) :
    ratios β τ h μ L n = {x | ∃ (r : Run β τ h μ L) (k : ℕ),
      r.stateSize k ≠ 0 ∧ x = r.stateSize (k+n) / r.stateSize k} := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, 0, hr, by simp⟩
  · rintro ⟨r, k, hr, rfl⟩
    exact ⟨r.shift k, by simpa using hr, by simp⟩

theorem ratios_bddAbove (β τ h μ L : ℝ) (hh : h ≠ 0) (hδ : determinant β τ ≠ 0) (n : ℕ) :
    BddAbove (insert 0 (ratios β τ h μ L n)) := by
  refine ⟨comparisonBound β τ h L * Rates.envelope (Momentum.method β τ h hh) μ L n, ?_⟩
  intro x hx
  rcases hx with rfl | ⟨r, hr, rfl⟩
  · exact mul_nonneg (comparisonBound_pos β τ h L).le (Rates.envelope_nonneg _ _ _ _)
  · apply (div_le_iff₀ (lt_of_le_of_ne (size_nonneg (r.pair 0)) (Ne.symm hr))).mpr
    exact size_correctionState_le r.admissible β τ h hh hδ r.initial n

theorem envelope_nonneg (β τ h μ L : ℝ) (hh : h ≠ 0) (hδ : determinant β τ ≠ 0) (n : ℕ) :
    0 ≤ envelope β τ h μ L n :=
  le_csSup (ratios_bddAbove β τ h μ L hh hδ n) (mem_insert _ _)

theorem envelope_le_source (β τ h μ L : ℝ) (hh : h ≠ 0) (hδ : determinant β τ ≠ 0) (n : ℕ) :
    envelope β τ h μ L n ≤ comparisonBound β τ h L *
      Rates.envelope (Momentum.method β τ h hh) μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r, hr, rfl⟩
  · exact mul_nonneg (comparisonBound_pos β τ h L).le (Rates.envelope_nonneg _ _ _ _)
  · apply (div_le_iff₀ (lt_of_le_of_ne (size_nonneg (r.pair 0)) (Ne.symm hr))).mpr
    exact size_correctionState_le r.admissible β τ h hh hδ r.initial n

theorem Run.stateSize_le_envelope {β τ h μ L : ℝ} (r : Run β τ h μ L)
    (hh : h ≠ 0) (hδ : determinant β τ ≠ 0) (hr : r.stateSize 0 ≠ 0) (n : ℕ) :
    r.stateSize n ≤ envelope β τ h μ L n * r.stateSize 0 := by
  apply (div_le_iff₀ (lt_of_le_of_ne (size_nonneg (r.pair 0)) (Ne.symm hr))).mp
  exact le_csSup (ratios_bddAbove β τ h μ L hh hδ n) (mem_insert_of_mem _ ⟨r, hr, rfl⟩)

theorem momentum_state_of_trajectory {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E} {β τ h : ℝ} (hh : h ≠ 0) {w : ℕ → E}
    (hw : (Momentum.method β τ h hh).IsTrajectory g w) (n : ℕ) :
    Momentum.state g β τ h (w 0) (w 1) n = (w n, w (n+1)) := by
  have hrec := (Momentum.method_trajectory_iff g β τ h hh w).mp hw
  induction n with
  | zero => rfl
  | succ n ih =>
    change Momentum.step g β τ h (Momentum.state g β τ h (w 0) (w 1) n) = _
    rw [ih]
    change (w (n+1), w (n+1) + β • (w (n+1)-w n) -
      h • g (w (n+1)+τ • (w (n+1)-w n))) = _
    rw [← hrec n]

theorem source_envelope_le (β τ h μ L : ℝ) (hh : h ≠ 0) (hδ : determinant β τ ≠ 0) (n : ℕ) :
    Rates.envelope (Momentum.method β τ h hh) μ L n ≤
      comparisonBound β τ h L * envelope β τ h μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r, hr, rfl⟩
  · exact mul_nonneg (comparisonBound_pos β τ h L).le (envelope_nonneg β τ h μ L hh hδ n)
  · let p : r.Carrier × r.Carrier := (r.w 0, r.w 1)
    let q := queryState (gradient r.f) β τ h p
    let s : Run β τ h μ L := ⟨r.Carrier, r.f, r.admissible, q⟩
    have hg := gradient_bound r.admissible
    have hstate (k : ℕ) : r.stateNorm k = size (Momentum.state (gradient r.f) β τ h p.1 p.2 k) := by
      rw [momentum_state_of_trajectory hh r.trajectory k]
      change Real.sqrt (∑ j : Fin 2, ‖r.w (k+j)‖ ^ 2) = _
      rw [Fin.sum_univ_two]
      rfl
    have hs (k : ℕ) : s.pair k = queryState (gradient r.f) β τ h
        (Momentum.state (gradient r.f) β τ h p.1 p.2 k) :=
      (state_conjugacy (gradient r.f) β τ h p k).symm
    have hback (k : ℕ) : r.stateNorm k ≤ inverseBound β τ h L * s.stateSize k := by
      rw [hstate k]
      have he : size (inverseState (gradient r.f) β τ h (s.pair k)) ≤
          inverseBound β τ h L * s.stateSize k := size_inverseState_le hg β τ h (s.pair k)
      rw [hs k, inverseState_queryState (gradient r.f) β τ h hδ] at he
      exact he
    have hs0 : s.stateSize 0 ≠ 0 := by
      intro hz
      have he := hback 0
      rw [hz, mul_zero] at he
      exact hr (le_antisymm he ((Momentum.method β τ h hh).stateNorm_nonneg r.w 0))
    have hforward : s.stateSize 0 ≤ forwardBound β τ h L * r.stateNorm 0 := by
      rw [hstate 0]
      change size (queryState (gradient r.f) β τ h p) ≤ forwardBound β τ h L * size p
      exact size_queryState_le hg β τ h p
    have hcorr := s.stateSize_le_envelope hh hδ hs0 n
    have hΓ := envelope_nonneg β τ h μ L hh hδ n
    have hsize : r.stateNorm n ≤ comparisonBound β τ h L * envelope β τ h μ L n * r.stateNorm 0 := by
      calc
        _ ≤ inverseBound β τ h L * s.stateSize n := hback n
        _ ≤ inverseBound β τ h L * (envelope β τ h μ L n * s.stateSize 0) :=
          mul_le_mul_of_nonneg_left hcorr (inverseBound_pos β τ h L).le
        _ ≤ inverseBound β τ h L * (envelope β τ h μ L n *
            (forwardBound β τ h L * r.stateNorm 0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hforward hΓ) (inverseBound_pos β τ h L).le
        _ = _ := by unfold comparisonBound; ring
    exact (div_le_iff₀ (lt_of_le_of_ne ((Momentum.method β τ h hh).stateNorm_nonneg r.w 0) (Ne.symm hr))).mpr hsize

/-- Literal uniform correction factor: the supremum is taken before the time limit. -/
def rate (β τ h μ L : ℝ) : ℝ :=
  limsup (fun n : ℕ => envelope β τ h μ L n ^ ((n : ℝ)⁻¹)) atTop

/-- The actual correction envelope has a genuine root limit. The forward and
inverse state bounds have constants independent of horizon, objective and dimension. -/
theorem tendsto_envelope_root {β τ h μ L : ℝ} (hh : h ≠ 0) (hδ : determinant β τ ≠ 0)
    (hμ : 0 < μ) (hμL : μ < L) :
    Tendsto (fun n : ℕ => envelope β τ h μ L n ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 (Momentum.momentumRate β τ h hh μ L)) := by
  let K := comparisonBound β τ h L
  have hK : 0 < K := comparisonBound_pos β τ h L
  have hg : ∀ n, 0 ≤ Rates.envelope (Momentum.method β τ h hh) μ L n :=
    Rates.envelope_nonneg _ _ _
  have hf : ∀ n, 0 ≤ envelope β τ h μ L n := envelope_nonneg β τ h μ L hh hδ
  have hlim := Rates.tendsto_envelope_root (Momentum.method β τ h hh) hμ hμL
  have hupperlim := (Rates.tendsto_const_root hK).mul hlim
  have hlowerlim := (Rates.tendsto_const_root (inv_pos.mpr hK)).mul hlim
  simp only [one_mul] at hupperlim hlowerlim
  have hupper (n : ℕ) : envelope β τ h μ L n ^ ((n : ℝ)⁻¹) ≤
      K ^ ((n : ℝ)⁻¹) * Rates.envelope (Momentum.method β τ h hh) μ L n ^ ((n : ℝ)⁻¹) := by
    calc
      _ ≤ (K * Rates.envelope (Momentum.method β τ h hh) μ L n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (hf n) (envelope_le_source β τ h μ L hh hδ n) (by positivity)
      _ = _ := Real.mul_rpow hK.le (hg n)
  have hlower (n : ℕ) : K⁻¹ ^ ((n : ℝ)⁻¹) *
      Rates.envelope (Momentum.method β τ h hh) μ L n ^ ((n : ℝ)⁻¹) ≤
        envelope β τ h μ L n ^ ((n : ℝ)⁻¹) := by
    have hn : K⁻¹ * Rates.envelope (Momentum.method β τ h hh) μ L n ≤ envelope β τ h μ L n := by
      calc
        _ ≤ K⁻¹ * (K * envelope β τ h μ L n) :=
          mul_le_mul_of_nonneg_left (source_envelope_le β τ h μ L hh hδ n) (inv_pos.mpr hK).le
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hK), one_mul]
    rw [← Real.mul_rpow (inv_pos.mpr hK).le (hg n)]
    exact Real.rpow_le_rpow (mul_nonneg (inv_pos.mpr hK).le (hg n)) hn (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerlim hupperlim hlower hupper

/-- Full uniform rate equality for arbitrary initial states on the original
smooth strongly convex class, under exactly the source nondegeneracy condition. -/
theorem rate_eq_momentumRate {β τ h μ L : ℝ} (hh : h ≠ 0) (hδ : determinant β τ ≠ 0)
    (hμ : 0 < μ) (hμL : μ < L) :
    rate β τ h μ L = Momentum.momentumRate β τ h hh μ L :=
  (tendsto_envelope_root hh hδ hμ hμL).limsup_eq

end nesterov.Momentum.Correction
