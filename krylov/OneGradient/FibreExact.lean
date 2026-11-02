import krylov.OneGradient.FibreMinimax
import krylov.OneGradient.XRFCOutputMaximum
import krylov.Methods.DirectionInformation
set_option autoImplicit false
/-!
Article: Theorem 4.1 [thm:exact] of krylov.tex.
Use: exhibit actual data-only XRFC policies in both bases attaining the least
uniform guarantee over the entire original physical fibre and output ball.
Source: the genuine arbitrary-method two-completion lower bound, actual XRFC
full-cycle output maximum and scalar harmonic equioscillation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods
variable {n : ℕ}

/-- A genuine data-only policy uses arbitrary earlier trial decisions and the
fixed information interval's harmonic trial at the prescribed final query.
Use: the actual trial receives only the observed transcript, with no hidden
completion parameter or unobserved output operator as an input.
Article: main_krylov, thm:exact.
Proof: the real transcript length identifies the final query count. -/
def harmonicLastTrial {E : Type*} (N : ℕ) (a b : ℝ) (earlier : History E → ℝ)
    (H : History E) : ℝ :=
  if H.records.length=N then harmonicTrial a b else earlier H

/-- Positive earlier data-only trials and positive interval endpoints give
an everywhere positive actual harmonic final-trial policy.
Use: derive every real XRFC inverse/basis domain before applying its executor theorem.
Article: main_krylov, thm:exact.
Proof: distinguish the actual observed query count and use the proved harmonic mean positivity. -/
theorem harmonic_last_trial_positive {E : Type*} (N : ℕ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) (earlier : History E → ℝ) (he : ∀ H,0<earlier H) (H : History E) :
    0<harmonicLastTrial N a b earlier H := by
  unfold harmonicLastTrial
  split
  · exact (harmonic_trial_attains ha hab).1
  · exact he H

/-- The two positive reciprocal physical endpoint pivots bound every actual
last CG length on the whole completion interval.
Use: connect the actual physical executor to the scalar harmonic interval theorem.
Article: main_krylov, thm:exact.
Proof: the genuine completion line is the reciprocal affine pivot; positivity
and order reverse the two physical endpoint inequalities. -/
theorem fibre_length_interval
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (blo bhi b : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (hb : b∈Set.Icc blo bhi) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    CG.length (cgOperator (lanczosCompletion A hA g hg hc b)) g n∈
      Set.Icc (1/(bhi-sigma)) (1/(blo-sigma)) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  have he : CG.length (cgOperator (lanczosCompletion A hA g hg hc b)) g n=1/(b-sigma) := by
    rw [completion_last_cg_length]
    dsimp only [sigma]
    congr 1
    ring
  rw [he]
  exact ⟨one_div_le_one_div_of_le (sub_pos.mpr (hlo.trans_le hb.1)) (sub_le_sub_right hb.2 sigma),
    one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right hb.1 sigma)⟩

/-- The harmonic trial's inverse is exactly the midpoint of the original
physical curvature interval measured above its common Schur threshold.
Use: identify the attaining rule with the source's printed reciprocal formula.
Article: main_krylov, thm:exact, tau^{-1}=(b_lo+b_hi)/2-sigma.
Proof: both actual pivot denominators are strictly positive; clear them and
compute the harmonic mean without an asymptotic approximation. -/
theorem harmonic_reciprocal_pivots {lo hi sigma : ℝ} (hlo : sigma<lo) (horder : lo≤hi) :
    (harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)))⁻¹=(lo+hi)/2-sigma := by
  have h1 : 0<lo-sigma := sub_pos.mpr hlo
  have h2 : 0<hi-sigma := sub_pos.mpr (hlo.trans_le horder)
  unfold harmonicTrial
  field_simp
  ring

/-- The actual step-basis full-memory XRFC harmonic policy attains the sharp
uniform physical fibre guarantee with arbitrary positive earlier trial decisions.
Use: every genuine completion in the whole closed interval and every admissible
physical output operator is covered, including zero output radius and a collapsed interval.
Article: main_krylov, thm:exact.
Proof: use actual full-atom exhaustion and positive trial domains in the proved
attained XRFC output maximum, then divide by the genuine positive CG error and
apply harmonic equioscillation to its actual last CG length. -/
theorem xrfc_fibre_harmonic_upper
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (blo bhi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (horder : blo≤bhi) (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (he : ∀ H,0<earlier H) {omega : ℝ} (homega : 0≤omega) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    let trial := harmonicLastTrial n (1/(bhi-sigma)) (1/(blo-sigma)) earlier
    ∀ b∈Set.Icc blo bhi,∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
      relativeBudget (lanczosCompletion A hA g hg hc b)
        (B-lanczosCompletion A hA g hg hc b)≤omega →
      fibreScenarioError A hA g hg hc (xrfcMethod fullMemory trial) b B≤
        omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma)) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let a := 1/(bhi-sigma)
  let c := 1/(blo-sigma)
  let trial := harmonicLastTrial n a c earlier
  have ha : 0<a := one_div_pos.mpr (sub_pos.mpr (hlo.trans_le horder))
  have hac : a≤c := one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  dsimp only
  intro b hb B hB hbudget
  let C := lanczosCompletion A hA g hg hc b
  let method := xrfcMethod fullMemory trial
  let H := oneGradientRun method (fun _ => cgOperator C) g (n+1)
  have hC : C.PosDef := (lanczos_completion_positive_iff A hA g hg hc b).mpr (hlo.trans_le hb.1)
  have hcount := completion_full_atoms A hA g hg hc b hC
  have ht (i : ℕ) (_hi : i<n+1) :
      trial (oneGradientRun method (fun _ => cgOperator C) g i)≠0 :=
    (harmonic_last_trial_positive n ha hac earlier he _).ne'
  have hmax := xrfc_last_output_maximum C hC g n hcount trial ht homega
  have htlast : trial (oneGradientRun method (fun _ => cgOperator C) g n)=harmonicTrial a c := by
    simp only [trial,harmonicLastTrial,oneGradientRun_length,ite_true]
  dsimp only at hmax
  rw [htlast] at hmax
  have hbound := hmax.2 ⟨B,hB,hbudget,rfl⟩
  have hlen := fibre_length_interval A hA g hg hc blo bhi b hlo hb
  have hscalar := trial_error_le_endpoints ha hlen.1 hlen.2 (harmonicTrial a c)
  rw [(harmonic_trial_attains ha hac).2] at hscalar
  change fibreScenarioError A hA g hg hc method b B≤omega*intervalMinimaxValue a c
  unfold fibreScenarioError
  apply (div_le_iff₀ (last_reference_denominator C hC g n hcount).1).mpr
  exact hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar homega) (norm_nonneg _))

/-- The actual direction-basis XRFC harmonic policy has the same sharp uniform
physical fibre guarantee, for every newest-retaining positive direction memory.
Use: full-memory XRFC-D is an attaining implementation in the original method class.
Article: main_krylov, thm:exact.
Proof: use the implemented direction-window full-cycle maximum and the same
true physical reciprocal-pivot interval and harmonic scalar bound. -/
theorem xrfcD_fibre_harmonic_upper
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (blo bhi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (horder : blo≤bhi) (memory : ℕ → ℕ) (hm : ∀ i≤n+1,0 < i → 0 < memory i)
    (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ) (he : ∀ H,0<earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    let trial := harmonicLastTrial n (1/(bhi-sigma)) (1/(blo-sigma)) earlier
    ∀ b∈Set.Icc blo bhi,∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
      relativeBudget (lanczosCompletion A hA g hg hc b)
        (B-lanczosCompletion A hA g hg hc b)≤omega →
      fibreScenarioError A hA g hg hc (xrfcDMethod memory trial) b B≤
        omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma)) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let a := 1/(bhi-sigma)
  let c := 1/(blo-sigma)
  let trial := harmonicLastTrial n a c earlier
  have ha : 0<a := one_div_pos.mpr (sub_pos.mpr (hlo.trans_le horder))
  have hac : a≤c := one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  dsimp only
  intro b hb B hB hbudget
  let C := lanczosCompletion A hA g hg hc b
  let method := xrfcDMethod memory trial
  have hC : C.PosDef := (lanczos_completion_positive_iff A hA g hg hc b).mpr (hlo.trans_le hb.1)
  have hcount := completion_full_atoms A hA g hg hc b hC
  have ht (i : ℕ) (_hi : i<n+1) :
      trial (oneGradientRun method (fun _ => cgOperator C) g i)≠0 :=
    (harmonic_last_trial_positive n ha hac earlier he _).ne'
  have hmax := xrfcD_last_output_maximum C hC g n hcount memory trial hm ht homega
  have htlast : trial (oneGradientRun method (fun _ => cgOperator C) g n)=harmonicTrial a c := by
    simp only [trial,harmonicLastTrial,oneGradientRun_length,ite_true]
  dsimp only at hmax
  rw [htlast] at hmax
  have hbound := hmax.2 ⟨B,hB,hbudget,rfl⟩
  have hlen := fibre_length_interval A hA g hg hc blo bhi b hlo hb
  have hscalar := trial_error_le_endpoints ha hlen.1 hlen.2 (harmonicTrial a c)
  rw [(harmonic_trial_attains ha hac).2] at hscalar
  change fibreScenarioError A hA g hg hc method b B≤omega*intervalMinimaxValue a c
  unfold fibreScenarioError
  apply (div_le_iff₀ (last_reference_denominator C hC g n hcount).1).mpr
  exact hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar homega) (norm_nonneg _))

/-- The complete physical fixed-fibre one-gradient minimax value is the least
uniform achievable error guarantee over all actual span-restricted methods.
Use: state a real minimum, with an explicit admissible attaining XRFC method,
and all original physical scenario quantifiers, rather than an abstract scalar surrogate.
Article: main_krylov, thm:exact.
Proof: actual full-memory harmonic XRFC supplies membership of the achievable
uniform-guarantee set; the arbitrary-method physical two-endpoint lower bound
forces every other guarantee above it. The ratio identity gives (r-1)/(r+1). -/
theorem fibre_exact_minimax
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (blo bhi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (horder : blo≤bhi) {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    IsLeast {q : ℝ | ∃ method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))),
      OneGradientSpanRestricted method ∧ ∀ b∈Set.Icc blo bhi,
        ∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
          relativeBudget (lanczosCompletion A hA g hg hc b)
            (B-lanczosCompletion A hA g hg hc b)≤omega →
          fibreScenarioError A hA g hg hc method b B≤q}
      (omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ :=
    harmonicLastTrial n (1/(bhi-sigma)) (1/(blo-sigma)) (fun _ => 1)
  constructor
  · refine ⟨xrfcMethod fullMemory trial,xrfcMethod_spanRestricted _ _,?_⟩
    exact xrfc_fibre_harmonic_upper A hA g hg hc blo bhi hlo horder (fun _ => 1) (fun _ => zero_lt_one) homega
  · rintro q ⟨method,hm,hbound⟩
    obtain ⟨b,hb,B,hB,hbudget,hlo'⟩ := fibre_method_endpoint_lower A hA g hg hc method hm blo bhi hlo horder homega hsmall
    have hb' : b∈Set.Icc blo bhi := by
      rcases Set.mem_insert_iff.mp hb with rfl|hb
      · exact ⟨le_rfl,horder⟩
      · have he : b=bhi := Set.mem_singleton_iff.mp hb
        subst b
        exact ⟨horder,le_rfl⟩
    exact hlo'.trans (hbound b hb' B hB hbudget)

end
end krylov.OneGradient
