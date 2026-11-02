import krylov.OneGradient.LastEvaluation
import krylov.OneGradient.InformationMoments
import krylov.OneGradient.TrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:exact, arbitrary-method two-endpoint lower bound.
Use: quantify over the original physical information fibre, actual admissible
one-gradient methods and real unobserved output matrices.
Source: actual nonanticipating history equality, CG conjugacy and scalar endpoint
equioscillation; no CG consistency is imposed on the competing method.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods
variable {n : ℕ}

/-- The original normalized physical one-gradient scenario error on the actual
last-Jacobi-pivot fibre.
Use: the last output operator is analysed semantically and never supplied to
either of the method's actual data-only decisions.
Article: main_krylov, s5:info and thm:exact.
Proof: use the genuine physical executor, inverse metric and penultimate CG error. -/
def fibreScenarioError
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))))
    (b : ℝ) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  let C := lanczosCompletion A hA g hg hc b
  ‖cgOperator (metricRoot C)⁻¹ (method.outputGradient (cgOperator B)
    (oneGradientRun method (fun _ => cgOperator C) g (n+1)))‖/‖cgCanonicalError C g n‖

/-- Every actual span-restricted method incurs the sharp fibrewise lower bound
on one of the two genuine endpoint completions, with an admissible real output matrix.
Use: establish the information lower bound for every method, including policies
whose final output depends on the last observed gradient and which are not CG-consistent.
Article: main_krylov, thm:exact.
Proof: choose the single common old-flag plus last-direction decomposition before
all completions. Genuine CG conjugacy controls each evaluated error, actual
symmetric output completion supplies its semantic lower bound, and the two
positive reciprocal pivots force the scalar harmonic minimax value. -/
theorem fibre_method_endpoint_lower
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))))
    (hm : OneGradientSpanRestricted method) (blo bhi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (horder : blo≤bhi) {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    ∃ b∈({blo,bhi} : Set ℝ),∃ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
      B.IsSymm ∧ relativeBudget (lanczosCompletion A hA g hg hc b)
        (B-lanczosCompletion A hA g hg hc b)≤omega ∧
      omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))≤
        fibreScenarioError A hA g hg hc method b B := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let Q := cgOperator A
  have hp := cgOperator_positive A hA
  have hfull := full_gradient_atom_count A hA g hc
  have hpre (j : ℕ) (hj : j<n+1) : CG.gradient Q g j≠0 :=
    cg_nonstagnation A hA g j (by rw [hfull];exact hj)
  have hlines (j : ℕ) (hj : j<n+1) : CG.length Q g j≠0 :=
    (CG.invariant_line_pos Q hp.2 g j
      (CG.invariant Q hp.1 hp.2 g j (fun i hi => hpre i (hi.trans hj))) (hpre j hj)).2.1.ne'
  obtain ⟨v,hv,t,hdec⟩ := one_gradient_information_decomposition method hm Q g n hlines
  have hone (b : ℝ) (hb : sigma<b) :
      ∃ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm ∧
        relativeBudget (lanczosCompletion A hA g hg hc b) (B-lanczosCompletion A hA g hg hc b)≤omega ∧
        omega*|1-t/(1/(b-sigma))|≤fibreScenarioError A hA g hg hc method b B := by
    let C := lanczosCompletion A hA g hg hc b
    let H := oneGradientRun method (fun _ => cgOperator C) g (n+1)
    have hC : C.PosDef := (lanczos_completion_positive_iff A hA g hg hc b).mpr hb
    have hcount := completion_full_atoms A hA g hg hc b hC
    have hact : ∀ w∈CG.krylovSpace Q g n,cgOperator C w=Q w :=
      lanczos_completion_information A hA g hg hc b
    have hvC : v∈CG.krylovSpace (cgOperator C) g n := by
      rw [information_krylov_space Q (cgOperator C) g n hact n (Nat.le_succ n)]
      exact hv
    have hdir : CG.direction (cgOperator C) g n=CG.direction Q g n :=
      congrArg CGState.direction (completion_cg_prefix A hA g hg hc b n le_rfl)
    have hpoint : H.displacement=CG.displacement (cgOperator C) g n+v+
        t • CG.direction (cgOperator C) g n := by
      have he := hdec (cgOperator C) hact
      rw [completion_cg_displacement A hA g hg hc b,hdir]
      change H.displacement-CG.displacement Q g n=v+t • CG.direction Q g n at he
      rw [sub_eq_iff_eq_add] at he
      rw [he]
      abel
    have hlength : CG.length (cgOperator C) g n=1/(b-sigma) := by
      rw [completion_last_cg_length]
      dsimp only [sigma]
      congr 1
      ring
    have heval := last_evaluation_lower C hC g n hcount v hvC t
    have hgrad : H.gradient=g+cgOperator C
        (CG.displacement (cgOperator C) g n+v+t • CG.direction (cgOperator C) g n) := by
      rw [show H.gradient=g+cgOperator C H.displacement from
        oneGradientRun_quadratic_gradient method (cgOperator C) g (n+1),hpoint]
    rw [← hgrad,hlength] at heval
    obtain ⟨B,hB,hbudget,hout⟩ := physical_output_lower C hC H.gradient (method.output H) homega hsmall
    refine ⟨B,hB,hbudget,?_⟩
    change omega*|1-t/(1/(b-sigma))|≤
      ‖cgOperator (metricRoot C)⁻¹ (H.gradient+cgOperator B (method.output H))‖/‖cgCanonicalError C g n‖
    apply (le_div_iff₀ (last_reference_denominator C hC g n hcount).1).mpr
    calc
      _ = omega*(|1-t/(1/(b-sigma))| *‖cgCanonicalError C g n‖) := by ring
      _ ≤ omega*‖cgOperator (metricRoot C)⁻¹ H.gradient‖ := mul_le_mul_of_nonneg_left heval homega
      _ ≤ _ := hout
  have hhi : sigma<bhi := hlo.trans_le horder
  have hapos : 0<1/(bhi-sigma) := one_div_pos.mpr (sub_pos.mpr hhi)
  have haorder : 1/(bhi-sigma)≤1/(blo-sigma) :=
    one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  have hscalar := mul_le_mul_of_nonneg_left (harmonic_trial_lower_bound hapos haorder t) homega
  dsimp only
  by_cases he : |1-t/(1/(bhi-sigma))|≤|1-t/(1/(blo-sigma))|
  · obtain ⟨B,hB,hbudget,hbound⟩ := hone blo hlo
    refine ⟨blo,Set.mem_insert _ _,B,hB,hbudget,?_⟩
    have hs : omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))≤
        omega*|1-t/(1/(blo-sigma))| := by
      simpa only [trialEndpointError,max_eq_right he] using hscalar
    exact hs.trans hbound
  · obtain ⟨B,hB,hbudget,hbound⟩ := hone bhi hhi
    refine ⟨bhi,Set.mem_insert_of_mem _ (Set.mem_singleton _),B,hB,hbudget,?_⟩
    have hs : omega*intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))≤
        omega*|1-t/(1/(bhi-sigma))| := by
      simpa only [trialEndpointError,max_eq_left (le_of_not_ge he)] using hscalar
    exact hs.trans hbound

end
end krylov.OneGradient
