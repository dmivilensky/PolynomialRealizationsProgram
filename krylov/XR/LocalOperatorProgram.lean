import krylov.XR.LocalTrialVector
import krylov.XR.OrdinaryValueIndependence

/-!
Article: main_krylov, lem:xr-local, actual finite operator-input program.
Use: reconstruct every real gradient query from its observed segment
operator. Auxiliary scalar slots use the fixed quadratic baseline; ordinary
XR ignores them by a separately proved literal code identity. At zero
operator perturbation all scalar and gradient slots are the true quadratic
observations. Thus primitive endpoint C² hypotheses derive operator-input
regularity of the native trial vector by finite induction.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference Filter Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real chronological endpoint program driven by segment operators.
The quadratic scalar slots are auxiliary coordinates ignored by ordinary
XR; gradients and query points are computed by the actual model rule. -/
def endpointOperatorRun (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (A : ℕ → E →L[ℝ] E) :
    (k : ℕ) → EndpointChart E k
  | 0 => (fun _ => 0, fun _ => constant, fun _ => g)
  | k+1 =>
    let C := endpointOperatorRun values trial Q g constant A k
    let x := endpointVirtualQuery values (trial k) C
    let v := C.2.2 (Fin.last k) + A k (x-C.1 (Fin.last k))
    extendEndpointChart C x (quadraticObjective Q g constant x, v)

omit [CompleteSpace E] in
/-- At the constant true quadratic every auxiliary slot is a genuine
scalar observation and every computed gradient is its actual gradient. -/
theorem endpointOperatorRun_quadratic (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (Q : E →L[ℝ] E)
    (g : E) (constant : ℝ) (k : ℕ) :
    endpointOperatorRun values trial Q g constant (fun _ => Q) k =
      endpointFunctionRun values trial (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k := by
  induction k with
  | zero => simp [endpointOperatorRun, endpointFunctionRun, quadraticObjective,
      krylov.Functions.quadraticPotential, quadraticGradient]
  | succ k ih =>
    rw [endpointOperatorRun, ih, endpointFunctionRun]
    congr 1
    apply Prod.ext
    · rfl
    let C := endpointFunctionRun values trial (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
    have hc := (endpointFunctionRun_cache values trial (quadraticObjective Q g constant)
      (quadraticGradient Q g) 0 k (Fin.last k)).2
    change C.2.2 (Fin.last k) + Q (_-C.1 (Fin.last k)) = _
    rw [hc]
    simp only [quadraticGradient, map_sub]
    abel

/-- True endpoint domains and primitive trials derive C² of the finite
operator-driven chart, with no trajectory regularity input. -/
theorem endpointOperatorRun_contDiffAt (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (Q : E →L[ℝ] E)
    (g : E) (constant : ℝ) (N : ℕ)
    (hdomains : ∀ k < N, EndpointProgramDomain values trial 0 constant g 2 k
      (adaptiveTranscript (endpointProgramQuery values trial 0 constant g)
        (fun x => (quadraticObjective Q g constant x, quadraticGradient Q g x)) k)) :
    ∀ k ≤ N, ContDiffAt ℝ 2 (fun e : Fin (N+1) → E →L[ℝ] E =>
      endpointOperatorRun values trial Q g constant (prescribedOperatorPath Q e) k) 0 := by
  intro k hk
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih =>
    have hkN : k < N := by omega
    have hC := ih hkN.le
    let C := fun e : Fin (N+1) → E →L[ℝ] E =>
      endpointOperatorRun values trial Q g constant (prescribedOperatorPath Q e) k
    have hz : C 0 = endpointProgramChart values trial 0 constant g k
        (adaptiveTranscript (endpointProgramQuery values trial 0 constant g)
          (fun x => (quadraticObjective Q g constant x, quadraticGradient Q g x)) k) := by
      rw [show C 0 = endpointOperatorRun values trial Q g constant (fun _ => Q) k from
        congrArg (fun A => endpointOperatorRun values trial Q g constant A k) (prescribedOperatorPath_zero Q N)]
      rw [endpointOperatorRun_quadratic, endpointFunctionRun_eq_program]
      simp [quadraticObjective, krylov.Functions.quadraticPotential, quadraticGradient]
    have hd := EndpointProgramDomain.current values trial 0 constant g 2 k _ (hdomains k hkN)
    rw [←hz] at hd
    have hq := contDiff_endpointVirtualQuery values C (trial k) 0 hC hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
    let x := fun e => endpointVirtualQuery values (trial k) (C e)
    have hx : ContDiffAt ℝ 2 x 0 := hq
    have hp := (contDiffAt_pi.mp hC.fst) (Fin.last k)
    have hg := (contDiffAt_pi.mp hC.snd.snd) (Fin.last k)
    have hA : ContDiffAt ℝ 2 (fun e : Fin (N+1) → E →L[ℝ] E => prescribedOperatorPath Q e k) 0 := by
      simp only [prescribedOperatorPath, dite_eq_left hkN]
      exact contDiffAt_const.add (contDiffAt_apply ℝ (E →L[ℝ] E) (⟨k, by omega⟩ : Fin (N+1)) 0)
    have hf : ContDiffAt ℝ 2 (fun e => quadraticObjective Q g constant (x e)) 0 := by
      change ContDiffAt ℝ 2 (fun e => inner ℝ (Q (x e)) (x e)/2 - -(inner ℝ g (x e)) + constant) 0
      exact (((contDiffAt_const.clm_apply hx).inner ℝ hx).div_const 2).sub
        ((contDiffAt_const.inner ℝ hx).neg) |>.add contDiffAt_const
    exact contDiff_extendEndpointChart C x _ 0 hC hx
      (hf.prodMk (hg.add (hA.clm_apply (hx.sub hp))))

end
end krylov.XR
