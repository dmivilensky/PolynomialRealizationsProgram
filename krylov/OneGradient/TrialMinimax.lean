import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, s5:trial(b).
Use: distinguish the harmonic trial for relative trial error from the arithmetic
estimate for the residual damping multiplier, including a collapsed interval.
Source: scalar Chebyshev equioscillation; the endpoint bounds and uniqueness are
proved here directly, without assuming existence of a minimax optimizer.
-/

namespace krylov.OneGradient
noncomputable section

/-- Worst relative trial error at the two endpoint completions.
Use: lower bounds require only the two indistinguishable endpoint completions.
Article: main_krylov, s5:trial(b).
Proof: take the maximum of the two actual relative errors. -/
def trialEndpointError (a b t : ℝ) : ℝ := max |1-t/a| |1-t/b|

/-- Worst residual damping multiplier at the two endpoint completions.
Use: DC-slide estimates minimize this quantity instead of the trial error.
Article: main_krylov, s5:trial(b).
Proof: take the maximum of the two actual damping multipliers. -/
def dampingEndpointError (a b t : ℝ) : ℝ := max |a/t-1| |b/t-1|

/-- Harmonic mean of the two positive possible exact step lengths.
Use: choose the attaining XRFC trial from the information interval.
Article: main_krylov, s5:trial(b).
Proof: the two endpoint relative trial errors equioscillate at this mean. -/
def harmonicTrial (a b : ℝ) : ℝ := 2*a*b/(a+b)

/-- Arithmetic mean of the two positive possible exact step lengths.
Use: choose the attaining DC-slide damping estimate.
Article: main_krylov, s5:trial(b).
Proof: the endpoint residual damping multipliers equioscillate at this mean. -/
def arithmeticEstimate (a b : ℝ) : ℝ := (a+b)/2

/-- Common minimax value, written without a potentially redundant ratio.
Use: the formula also covers an information interval consisting of one point.
Article: main_krylov, s5:trial(b).
Proof: normalize the length of the positive interval by its endpoint sum. -/
def intervalMinimaxValue (a b : ℝ) : ℝ := (b-a)/(b+a)

private theorem abs_le_endpoint_max {x y z : ℝ} (hxy : x≤y) (hyz : y≤z) :
    |y|≤max |x| |z| := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |x| |z|)).trans ((neg_abs_le x).trans hxy)
  · exact hyz.trans ((le_abs_self z).trans (le_max_right |x| |z|))

/-- No interior exact step has a larger relative trial error than both endpoints.
Use: turn the two-point minimax computation into the full information-interval bound.
Article: main_krylov, s5:trial(b).
Proof: division by a positive exact step is monotone in its denominator, with
the order reversed when the trial changes sign. -/
theorem trial_error_le_endpoints {a b x : ℝ} (ha : 0<a) (hax : a≤x)
    (hxb : x≤b) (t : ℝ) : |1-t/x|≤trialEndpointError a b t := by
  have hx : 0<x := ha.trans_le hax
  have hb : 0<b := hx.trans_le hxb
  by_cases ht : 0≤t
  · apply abs_le_endpoint_max (x := 1-t/a) (z := 1-t/b)
    · linarith [div_le_div_of_nonneg_left ht ha hax]
    · linarith [div_le_div_of_nonneg_left ht hx hxb]
  · have hn : 0≤-t := by linarith
    have h1 := div_le_div_of_nonneg_left hn ha hax
    have h2 := div_le_div_of_nonneg_left hn hx hxb
    simp only [neg_div] at h1 h2
    simpa only [trialEndpointError, max_comm] using
      abs_le_endpoint_max (by linarith : 1-t/b≤1-t/x) (by linarith : 1-t/x≤1-t/a)

/-- No interior exact step has a larger damping multiplier than both endpoints.
Use: the DC-slide estimate controls every admissible completion.
Article: main_krylov, s5:trial(b).
Proof: division by the positive chosen estimate preserves the interval order. -/
theorem damping_error_le_endpoints {a b x t : ℝ} (hax : a≤x) (hxb : x≤b)
    (ht : 0<t) : |x/t-1|≤dampingEndpointError a b t := by
  exact abs_le_endpoint_max (by exact sub_le_sub_right (div_le_div_of_nonneg_right hax ht.le) 1)
    (by exact sub_le_sub_right (div_le_div_of_nonneg_right hxb ht.le) 1)

private theorem trial_constraints {a b t c : ℝ} (ha : 0<a) (hb : 0<b)
    (h : trialEndpointError a b t≤c) : b*(1-c)≤t ∧ t≤a*(1+c) := by
  have h1 := (abs_le.mp ((le_max_left |1-t/a| |1-t/b|).trans h)).1
  have h2 := (abs_le.mp ((le_max_right |1-t/a| |1-t/b|).trans h)).2
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hb).mp (by linarith : 1-c≤t/b)
  · simpa only [mul_comm] using (div_le_iff₀ ha).mp (by linarith : t/a≤1+c)

/-- Every real trial has error at least the printed minimax value.
Use: two endpoint completions already give the scalar lower bound, even for
a method choosing a nonpositive trial.
Article: main_krylov, s5:trial(b).
Proof: add the endpoint inequalities after clearing their positive denominators. -/
theorem harmonic_trial_lower_bound {a b : ℝ} (ha : 0<a) (hab : a≤b) (t : ℝ) :
    intervalMinimaxValue a b≤trialEndpointError a b t := by
  have hb := ha.trans_le hab
  obtain ⟨hl,hu⟩ := trial_constraints ha hb (le_refl (trialEndpointError a b t))
  apply (div_le_iff₀ (by linarith : 0<b+a)).mpr
  nlinarith

/-- The harmonic trial is positive and its two endpoint errors attain the bound.
Use: construct a valid positive XRFC trial, including a singleton interval.
Article: main_krylov, s5:trial(b).
Proof: substitute the actual harmonic mean; the two errors are opposite and
their common absolute value is nonnegative. -/
theorem harmonic_trial_attains {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    0<harmonicTrial a b ∧
      trialEndpointError a b (harmonicTrial a b)=intervalMinimaxValue a b := by
  have hb := ha.trans_le hab
  have hs : 0<a+b := add_pos ha hb
  have hv : 0≤ intervalMinimaxValue a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have e1 : 1-harmonicTrial a b/a= -intervalMinimaxValue a b := by
    unfold harmonicTrial intervalMinimaxValue
    field_simp
    ring
  have e2 : 1-harmonicTrial a b/b=intervalMinimaxValue a b := by
    unfold harmonicTrial intervalMinimaxValue
    field_simp
    ring
  refine ⟨div_pos (by positivity) hs, ?_⟩
  simp only [trialEndpointError,e1,e2,abs_neg,abs_of_nonneg hv,max_self]

/-- The harmonic trial is the unique minimizer among all real trials.
Use: identify the one-gradient optimal rule, rather than merely an upper bound.
Article: main_krylov, s5:trial(b).
Proof: at the minimal error the lower and upper endpoint constraints meet at
the harmonic mean. The proof includes coincident positive endpoints. -/
theorem harmonic_trial_unique {a b : ℝ} (ha : 0<a) (hab : a≤b) (t : ℝ) :
    trialEndpointError a b t≤ intervalMinimaxValue a b ↔ t=harmonicTrial a b := by
  have hb := ha.trans_le hab
  constructor
  · intro ht
    obtain ⟨hl,hu⟩ := trial_constraints ha hb ht
    have el : b*(1-intervalMinimaxValue a b)=harmonicTrial a b := by
      unfold intervalMinimaxValue harmonicTrial
      field_simp
      ring
    have eu : a*(1+intervalMinimaxValue a b)=harmonicTrial a b := by
      unfold intervalMinimaxValue harmonicTrial
      field_simp
      ring
    rw [el] at hl
    rw [eu] at hu
    exact le_antisymm hu hl
  · rintro rfl
    exact (harmonic_trial_attains ha hab).2.le

private theorem damping_constraints {a b t c : ℝ} (ht : 0<t)
    (h : dampingEndpointError a b t≤c) : t*(1-c)≤a ∧ b≤t*(1+c) := by
  have h1 := (abs_le.mp ((le_max_left |a/t-1| |b/t-1|).trans h)).1
  have h2 := (abs_le.mp ((le_max_right |a/t-1| |b/t-1|).trans h)).2
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ ht).mp (show 1-c≤a/t by linarith)
  · simpa only [mul_comm] using (div_le_iff₀ ht).mp (show b/t≤1+c by linarith)

/-- Every positive damping estimate has error at least the same minimax value.
Use: the last-pivot uncertainty forces a DC-slide residual damping lower bound.
Article: main_krylov, s5:trial(b).
Proof: multiply the two cleared endpoint constraints by the opposite positive
endpoint; positivity of the chosen estimate cancels the remaining factor. -/
theorem arithmetic_estimate_lower_bound {a b t : ℝ} (ha : 0<a) (hab : a≤b)
    (ht : 0<t) : intervalMinimaxValue a b≤dampingEndpointError a b t := by
  have hb := ha.trans_le hab
  obtain ⟨hl,hu⟩ := damping_constraints ht (le_refl (dampingEndpointError a b t))
  apply (div_le_iff₀ (by linarith : 0<b+a)).mpr
  have h := (mul_le_mul_of_nonneg_left hl hb.le).trans
    (by simpa only [mul_comm a b] using mul_le_mul_of_nonneg_left hu ha.le)
  nlinarith

/-- The arithmetic estimate is positive and attains the endpoint damping bound.
Use: supply the actual minimax DC-slide estimate.
Article: main_krylov, s5:trial(b).
Proof: substitution makes the two endpoint damping multipliers opposite. -/
theorem arithmetic_estimate_attains {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    0<arithmeticEstimate a b ∧
      dampingEndpointError a b (arithmeticEstimate a b)=intervalMinimaxValue a b := by
  have hb := ha.trans_le hab
  have hv : 0≤ intervalMinimaxValue a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have e1 : a/arithmeticEstimate a b-1= -intervalMinimaxValue a b := by
    unfold arithmeticEstimate intervalMinimaxValue
    field_simp
    ring
  have e2 : b/arithmeticEstimate a b-1=intervalMinimaxValue a b := by
    unfold arithmeticEstimate intervalMinimaxValue
    field_simp
    ring
  refine ⟨by unfold arithmeticEstimate; positivity, ?_⟩
  simp only [dampingEndpointError,e1,e2,abs_neg,abs_of_nonneg hv,max_self]

/-- The arithmetic estimate uniquely minimizes damping over positive estimates.
Use: prevent replacing the DC-slide estimate by the different harmonic trial.
Article: main_krylov, s5:trial(b).
Proof: at the minimal value both cleared endpoint inequalities determine the
same estimate, also when the two possible exact steps coincide. -/
theorem arithmetic_estimate_unique {a b t : ℝ} (ha : 0<a) (hab : a≤b)
    (ht : 0<t) : dampingEndpointError a b t≤ intervalMinimaxValue a b ↔
      t=arithmeticEstimate a b := by
  have hb := ha.trans_le hab
  constructor
  · intro he
    obtain ⟨hl,hu⟩ := damping_constraints ht he
    have e1 : 1-intervalMinimaxValue a b=2*a/(a+b) := by
      unfold intervalMinimaxValue
      field_simp
      ring
    have e2 : 1+intervalMinimaxValue a b=2*b/(a+b) := by
      unfold intervalMinimaxValue
      field_simp
      ring
    rw [e1] at hl
    rw [e2] at hu
    have hs : 0<a+b := add_pos ha hb
    have hl' := (div_le_iff₀ hs).mp (show t*(2*a)/(a+b)≤a by simpa [mul_div_assoc] using hl)
    have hu' := (le_div_iff₀ hs).mp (show b≤t*(2*b)/(a+b) by simpa [mul_div_assoc] using hu)
    unfold arithmeticEstimate
    apply le_antisymm <;> nlinarith
  · rintro rfl
    exact (arithmetic_estimate_attains ha hab).2.le

/-- The endpoint maximum is the attained worst error over the full closed interval.
Use: the scalar minimax result quantifies over every admissible exact step.
Article: main_krylov, s5:trial(b).
Proof: monotonicity bounds interior points and one of the two endpoints attains
their maximum. -/
theorem trial_interval_worst {a b : ℝ} (ha : 0<a) (hab : a≤b) (t : ℝ) :
    IsGreatest ((fun x : ℝ => |1-t/x|) '' Set.Icc a b) (trialEndpointError a b t) := by
  constructor
  · rcases le_total |1-t/a| |1-t/b| with h|h
    · exact ⟨b,⟨hab,le_rfl⟩,(max_eq_right h).symm⟩
    · exact ⟨a,⟨le_rfl,hab⟩,(max_eq_left h).symm⟩
  · rintro _ ⟨x,⟨hax,hxb⟩,rfl⟩
    exact trial_error_le_endpoints ha hax hxb t

/-- The damping endpoint maximum is the attained worst error over the full interval.
Use: arithmetic damping controls all feasible completions, including endpoints.
Article: main_krylov, s5:trial(b).
Proof: the affine multiplier has no larger absolute value at an interior point. -/
theorem damping_interval_worst {a b t : ℝ} (hab : a≤b) (ht : 0<t) :
    IsGreatest ((fun x : ℝ => |x/t-1|) '' Set.Icc a b) (dampingEndpointError a b t) := by
  constructor
  · rcases le_total |a/t-1| |b/t-1| with h|h
    · exact ⟨b,⟨hab,le_rfl⟩,(max_eq_right h).symm⟩
    · exact ⟨a,⟨le_rfl,hab⟩,(max_eq_left h).symm⟩
  · rintro _ ⟨x,⟨hax,hxb⟩,rfl⟩
    exact damping_error_le_endpoints hax hxb ht

/-- The harmonic rule gives the actual minimum over all real trials.
Use: an exact scalar minimax equality, with existence proved constructively.
Article: main_krylov, s5:trial(b).
Proof: combine the endpoint lower bound with the proved attaining positive trial. -/
theorem harmonic_trial_minimax {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IsLeast (Set.range (trialEndpointError a b)) (intervalMinimaxValue a b) := by
  exact ⟨⟨harmonicTrial a b,(harmonic_trial_attains ha hab).2⟩,
    by rintro _ ⟨t,rfl⟩; exact harmonic_trial_lower_bound ha hab t⟩

/-- The arithmetic rule gives the actual minimum over positive damping estimates.
Use: the exact second minimax problem in the article.
Article: main_krylov, s5:trial(b).
Proof: the attaining arithmetic estimate is positive and every positive estimate
satisfies the endpoint lower bound. -/
theorem arithmetic_estimate_minimax {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IsLeast ((dampingEndpointError a b) '' Set.Ioi 0) (intervalMinimaxValue a b) := by
  exact ⟨⟨arithmeticEstimate a b,(arithmetic_estimate_attains ha hab).1,
      (arithmetic_estimate_attains ha hab).2⟩,
    by rintro _ ⟨t,ht,rfl⟩; exact arithmetic_estimate_lower_bound ha hab ht⟩

/-- The minimax value is precisely the article's condition-ratio expression.
Use: substitute a spectral or relative-ball information ratio.
Article: main_krylov, s5:trial(b).
Proof: clear the positive lower endpoint from the ratio. -/
theorem interval_minimax_ratio {a b : ℝ} (ha : 0<a) :
    intervalMinimaxValue a b=(b/a-1)/(b/a+1) := by
  unfold intervalMinimaxValue
  field_simp

/-- At the harmonic trial, the opposite damping objective has the larger value.
Use: quantify the price of using the trial minimax rule for DC-slide damping.
Article: main_krylov, s5:trial(b).
Proof: the two signed endpoint values are the article's asymmetric interval;
the positive endpoint has the larger absolute value. -/
theorem harmonic_damping_error {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    dampingEndpointError a b (harmonicTrial a b)=(b-a)/(2*a) := by
  have hb := ha.trans_le hab
  have e1 : a/harmonicTrial a b-1= -(b-a)/(2*b) := by
    unfold harmonicTrial
    field_simp
    ring
  have e2 : b/harmonicTrial a b-1=(b-a)/(2*a) := by
    unfold harmonicTrial
    field_simp
    ring
  have hn : 0≤b-a := sub_nonneg.mpr hab
  have hba : (b-a)/(2*b)≤(b-a)/(2*a) :=
    div_le_div_of_nonneg_left hn (by positivity) (by linarith)
  simp only [dampingEndpointError,e1,e2,neg_div,abs_neg,
    abs_of_nonneg (show 0≤(b-a)/(2*a) from div_nonneg hn (by positivity)),
    abs_of_nonneg (show 0≤(b-a)/(2*b) from div_nonneg hn (by positivity)),max_eq_right hba]

/-- At the arithmetic estimate, the opposite trial objective has the larger value.
Use: quantify the trial error from using the residual damping minimax rule in XRFC.
Article: main_krylov, s5:trial(b).
Proof: the two signed endpoint errors are opposite asymmetric fractions, with
the negative endpoint having the larger absolute value. -/
theorem arithmetic_trial_error {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    trialEndpointError a b (arithmeticEstimate a b)=(b-a)/(2*a) := by
  have hb := ha.trans_le hab
  have e1 : 1-arithmeticEstimate a b/a= -(b-a)/(2*a) := by
    unfold arithmeticEstimate
    field_simp
    ring
  have e2 : 1-arithmeticEstimate a b/b=(b-a)/(2*b) := by
    unfold arithmeticEstimate
    field_simp
    ring
  have hn : 0≤b-a := sub_nonneg.mpr hab
  have hba : (b-a)/(2*b)≤(b-a)/(2*a) :=
    div_le_div_of_nonneg_left hn (by positivity) (by linarith)
  simp only [trialEndpointError,e1,e2,neg_div,abs_neg,
    abs_of_nonneg (show 0≤(b-a)/(2*a) from div_nonneg hn (by positivity)),
    abs_of_nonneg (show 0≤(b-a)/(2*b) from div_nonneg hn (by positivity)),max_eq_left hba]

end
end krylov.OneGradient
