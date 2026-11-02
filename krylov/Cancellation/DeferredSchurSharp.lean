import krylov.Cancellation.DeferredSchurNative
import krylov.Cancellation.DeferredSourceTheorem
import krylov.Cancellation.DeferredCompactSharp
import krylov.Cancellation.DeferredRadauComparison
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original smooth arithmetic interval policy.
Use: the concrete deferred Schur continuation has the full nonlinear sharp
source expansion and compact weighted remainder, with no estimate premises.
Source: actual native reference charts and the existing genuine deferred
worst-output and sharp compact source theorems.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual smooth arithmetic interval deferred executor has the full
original nonlinear supremum expansion with a common largest-budget
quadratic remainder, including zero budgets and physical band endpoints.
Use: no smoothness or positivity premise is left for a chosen estimate.
Article: main_krylov, thm:DC, concrete interval-policy sharp expansion.
Proof: its actual reference dictionary supplies the original positive
final estimate and C-two chart; specialize the proved native sharp theorem. -/
theorem deferred_schur_sharp_expansion
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n) :
    let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let epsilon := 1-CG.length Q g k/a0
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ omegaBar : ℝ,0≤omegaBar → omegaBar≤delta →
      ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∀ l<k,omega l≤omegaBar) →
      |deferredWorstOutput estimate base g k omega-deferredSharpCoefficient base g k epsilon omega|≤C*omegaBar^2 := by
  dsimp only
  let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
  have hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have hdata := deferred_schur_reference_data fullMemory (fun _ hj => hj) (k+1)
    base hb mu upper hmu hmuL hlo hhi g k hpre 2
  exact deferred_data_sharp_expansion estimate base hb g k hcount hfull hdata.2.1 hdata.1

/-- The actual smooth arithmetic Schur deferred policy has the original
positive estimate and physical spectral damping factor, with its true
known CG length and actual final observed reference history.
Use: the original sharp FC comparison applies to this concrete continuation.
Article: main_krylov, thm:DC, actual continued interval damping.
Proof: the raw interval and Schur estimates agree on the same genuine
quadratic history; complete deferred histories for both rules equal FC.
Transfer the already proved original physical damping inequality. -/
theorem deferred_schur_reference_damping
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (horizon : ℕ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0) :
    let Q := cgOperator base
    let estimate := dcSchurGaussRadauEstimate memory mu upper (n := n)
    let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k
    0<estimate H ∧ |1-CG.length Q g k/estimate H|≤(upper-mu)/(upper+mu) := by
  let Q := cgOperator base
  let es := dcSchurGaussRadauEstimate memory mu upper (n := n)
  let er := dcGaussRadauEstimate memory mu upper (n := n)
  let HS := methodRun (deferredDataMethod memory horizon es) (fun _ => Q) (fun _ => Q) g k
  let HR := methodRun (deferredDataMethod memory horizon er) (fun _ => Q) (fun _ => Q) g k
  have hp := cgOperator_positive base hb
  have hhistory : HR=HS := (deferred_data_reference_run memory hm horizon er Q hp.1 hp.2 g k).trans
    (deferred_data_reference_run memory hm horizon es Q hp.1 hp.2 g k).symm
  have heq : er HS=es HS := (deferred_schur_reference_data memory hm horizon base hb mu upper
    hmu hmuL hlo hhi g k hpre 2).2.2
  have h := deferred_gauss_radau_reference_damping memory hm horizon base hb mu upper hmu hmuL hlo hhi g k (hpre k (by omega))
  change 0<er HR ∧ |1-CG.length Q g k/er HR|≤(upper-mu)/(upper+mu) at h
  rw [hhistory,heq] at h
  exact h

/-- The original observed arithmetic deferred policy reduces the real full
FC sharp coefficient, strictly at every positive intermediate source budget.
Use: all scalar damping and physical completion domains come from the
implemented native policy's true reference history.
Article: main_krylov, thm:DC, actual Gauss--Radau sharp FC improvement.
Proof: the real observed arithmetic estimate has the proved class spectral
damping bound, strictly below one because the original lower spectral bound
is positive. Apply the genuine full actual CG-tail coefficient comparisons,
including the printed exact intermediate-budget strictness condition. -/
theorem deferred_schur_FC_improvement
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g=k+1)
    (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    let Q := cgOperator base
    let estimate := dcSchurGaussRadauEstimate fullMemory mu L (n := n)
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let epsilon := 1-CG.length Q g k/a0
    (∑ l∈Finset.range k,omega l*‖deferredTail base g k epsilon l‖)≤
      (∑ l∈Finset.range k,omega l*‖cgCanonicalError base g (l+1)‖) ∧
      ((∃ l,l+1<k ∧ 0<omega l) →
        (∑ l∈Finset.range k,omega l*‖deferredTail base g k epsilon l‖)<
          ∑ l∈Finset.range k,omega l*‖cgCanonicalError base g (l+1)‖) := by
  have hc := deferred_schur_reference_damping fullMemory (fun _ hj => hj) (k+1)
    base hb mu L hmu hmuL hlo hhi g k (fun i hi => cg_nonstagnation base hb g i (by omega))
  have hrho : (L-mu)/(L+mu)<1 := by
    apply (div_lt_one (add_pos (hmu.trans_le hmuL) hmu)).mpr
    linarith
  have hepsilon := hc.2.trans_lt hrho
  exact ⟨deferred_full_coefficient_le_FC base hb g k hstop _ hepsilon.le omega homega,
    fun hp => deferred_full_coefficient_strict_FC base hb g k hstop _ hepsilon omega homega hp⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The literal deferred Schur interval policy has the full original
compact-uniform nonlinear supremum expansion, with one common radius and
initial-error-weighted largest-budget quadratic constant before all
reference points, source matrices and individual nonnegative profiles.
Use: all actual estimate/chart hypotheses are discharged at genuine
physical-band references, including class endpoint spectra.
Article: main_krylov, thm:DC, concrete full compact sharp source conclusion.
Proof: derive the genuine positive C-two final observed estimate at each
actual reference. Reuse the complete original compact supremum theorem;
its actual physical maximum and common Taylor remainder are unchanged. -/
theorem deferred_schur_compact_sharp_expansion
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x)
    (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (hlo : ∀ x∈K,(base x-mu • 1).PosSemidef)
    (hhi : ∀ x∈K,(upper • 1-base x).PosSemidef) :
    let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
    let m := deferredDataMethod fullMemory (k+1) estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ omegaBar : ℝ,0≤omegaBar → omegaBar≤delta →
      ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∀ l<k,omega l≤omegaBar) →
      let Q := cgOperator (base x)
      let R := cgOperator (metricRoot (base x))⁻¹
      let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
      |deferredWorstOutput estimate (base x) (g x) k omega-
        deferredSharpCoefficient (base x) (g x) k (1-CG.length Q (g x) k/a0) omega|≤C*omegaBar^2*‖R (g x)‖ := by
  dsimp only
  let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
  have hdata (x : X) (hx : x∈K) := deferred_schur_reference_data fullMemory (fun _ hj => hj) (k+1)
    (base x) (hpos x hx).self_of_nhds mu upper hmu hmuL (hlo x hx) (hhi x hx) (g x) k
    (fun i hi => cg_nonstagnation (base x) (hpos x hx).self_of_nhds (g x) i (by rw [hcount x hx];omega)) 2
  exact deferred_data_compact_sharp_expansion estimate base g k hfull K hK hb hpos hg hcount
    (fun x hx => (hdata x hx).2.1) (fun x hx => (hdata x hx).1)

end
end krylov.Cancellation
