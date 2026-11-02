import krylov.Convergence.OneGradientCubicAttainment
import krylov.OneGradient.ObservedPriorAttainment

/-!
Article: main_krylov, thm:LB, last sentence, actual harmonic cubic attainment.
Use: one genuine observed-prior last-trial policy gives the exact rank-one
scalar-function returned gradient and the original information coefficient.
Every last-axis, nonstagnation and interval premise is derived from the
actual full-atom SPD reference and its realizable known prior.
Source: actual observed harmonic dictionary and native two-basis cubic replay.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The single known-prior harmonic last-trial rule attains the printed
function-level rank-one value and the true information-fibre upper bound
in both implemented XRFC bases. Article: main_krylov, thm:LB. -/
theorem xrfcBasis_observed_harmonic_cubic_attainment
    (directions : Bool) (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef)
    (g : E) (hg : g≠0) (hc : (activeSpectralValues A hA.1 g).card=k+1)
    (prior : Set (Matrix (Fin (k+1)) (Fin (k+1)) ℝ)) (lo hi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<lo)
    (horder : lo≤hi)
    (hprior : ∀ b : ℝ,lanczosCompletion A hA g hg hc b∈prior ↔ b∈Icc lo hi)
    (hmem : A∈prior) (earlier : History E → ℝ) (he : ∀ H,0<earlier H) (t : ℝ) :
    let sigma:=lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    let trial:=observedPriorLastTrial k prior earlier
    let method:=xrfcBasisMethod directions trial
    let a:=lastLanczosVector A hA g hg hc
    let p:=inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
    let G:=oneGradientCubicFibreGradient (cgOperator A) g a (-t*p/2) t
    oneGradientFunctionOutput method G 0 (k+1)=oneGradientQuadraticMinimizer A g ∧
      ‖cgOperator (metricRoot A)⁻¹ (G (oneGradientFunctionOutput method G 0 (k+1)))‖=
        |t|/2*‖cgOperator (metricRoot A)⁻¹ a‖^3*
          |1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k| *
          ‖cgCanonicalError A g k‖^2 ∧
      |1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k|≤
        intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma)) := by
  let sigma:=lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let trial:=observedPriorLastTrial k prior earlier
  let method:=xrfcBasisMethod directions trial
  let a:=lastLanczosVector A hA g hg hc
  have hfull:=full_gradient_atom_count A hA g hc
  have htH (H : History E) : 0<trial H:=observed_prior_last_trial_positive k prior earlier he H
  have hpre i (hi : i<k+1):=cg_nonstagnation A hA g i (by rw [hfull];exact hi)
  have hhist:=xrfc_quadratic_basis_histories trial (cgOperator A) (cgOperator_positive A hA).1
    (cgOperator_positive A hA).2 g (k+1) hpre (fun _ _=>(htH _).ne')
  let J:=oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator A) g k
  have hraw:=xrfc_observed_prior_harmonic A hA g hg hc trial (fun _ _=>(htH _).ne')
    prior lo hi hlo horder hprior
  have htrial : trial J=harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)) := by
    change observedPriorLastTrial k prior earlier J=_
    rw [observedPriorLastTrial,oneGradientRun_length,ite_eq_left rfl,ite_eq_left hraw.1]
    exact hraw.2
  have hself : lanczosCompletion A hA g hg hc (lastJacobiPivot A hA g hg hc)=A := by
    simp only [lanczosCompletion,sub_self,zero_smul,add_zero]
  have hmember : lastJacobiPivot A hA g hg hc∈Icc lo hi :=
    (hprior _).mp (by rw [hself];exact hmem)
  have hlength:=fibre_length_interval A hA g hg hc lo hi _ hlo hmember
  rw [hself] at hlength
  have ha : 0<1/(hi-sigma):=one_div_pos.mpr (sub_pos.mpr (hlo.trans_le horder))
  have hab : 1/(hi-sigma)≤1/(lo-sigma):=
    one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  have herr:=trial_error_le_endpoints ha hlength.1 hlength.2
    (harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)))
  rw [(harmonic_trial_attains ha hab).2] at herr
  have hlast : |1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k|≤
      intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma)) := by
    have hj : oneGradientRun method (fun _=>cgOperator A) g k=J := by
      cases directions with
      | false=>rfl
      | true=>exact hhist k (by omega)
    rw [hj,htrial]
    exact herr
  have hactual:=xrfcBasis_cubic_actual_attainment directions trial A hA g a
    (last_lanczos_unit A hA g hg hc) hfull (krylov_last_lanczos_hyperplane A hA g hg hc)
    (fun _ _=>(htH _).ne') t
  exact ⟨hactual.1,hactual.2,hlast⟩

end
end krylov.Convergence
