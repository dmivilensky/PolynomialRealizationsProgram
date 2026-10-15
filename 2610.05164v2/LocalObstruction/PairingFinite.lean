import «2610.05164v2».LocalObstruction.KernelPairing
import «2610.05164v2».LocalObstruction.VolterraPerturbation

/-!
Article: 2610.05164v2, Theorem 6.1.
Finite signed families of the actual square-trace pairing are quadratic polynomials in their
coefficients.
Use: `«2610.05164v2».LocalObstruction.pairing_finite_smooth` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open MeasureTheory Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Exact identity `pairing (fun x => ∑ i,v i x) m=∑ i,pairing (v i) m`.

Use: `«2610.05164v2».LocalObstruction.pairing_perturb` rewrites with this identity to establish
exact identity `pairing (perturb m v a) (perturb m v a)=pairing m m+ (∑ i,a i*pairing (v i)
m)+(∑ i,a i*pairing m (v i))+ ∑ i,∑ j,a i*a j*pairing (v i) (v j)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.pairing_integrable` with
the arguments shown in the proof.
-/
theorem pairing_sum_left {ι : Type*} [Fintype ι] {v : ι → ℝ → ℝ} {m : ℝ → ℝ}
    (hv : ∀ i,Integrable (v i)) (hm : Integrable m) :
    pairing (fun x => ∑ i,v i x) m=∑ i,pairing (v i) m := by
  unfold pairing
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => pairing_integrable (hv i) hm)

 /--
Exact identity `pairing m (fun x => ∑ i,v i x)=∑ i,pairing m (v i)`.

Use: `«2610.05164v2».LocalObstruction.pairing_perturb` rewrites with this identity to establish
exact identity `pairing (perturb m v a) (perturb m v a)=pairing m m+ (∑ i,a i*pairing (v i)
m)+(∑ i,a i*pairing m (v i))+ ∑ i,∑ j,a i*a j*pairing (v i) (v j)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem pairing_sum_right {ι : Type*} [Fintype ι] {v : ι → ℝ → ℝ} {m : ℝ → ℝ}
    (hv : ∀ i,Integrable (v i)) (hm : Integrable m) :
    pairing m (fun x => ∑ i,v i x)=∑ i,pairing m (v i) := by
  rw [pairing_symm hm (integrable_finsetSum _ (fun i _ => hv i)),pairing_sum_left hv hm]
  apply Finset.sum_congr rfl
  intro i _
  exact pairing_symm (hv i) hm

 /--
Exact identity `pairing (perturb m v a) (perturb m v a)=pairing m m+ (∑ i,a i*pairing (v i)
m)+(∑ i,a i*pairing m (v i))+ ∑ i,∑ j,a i*a j*pairing (v i) (v j)`.

Use: `«2610.05164v2».LocalObstruction.pairing_finite_smooth` uses this identity to establish
smoothness to the stated order: `ContDiff ℝ ∞ (fun a : ι → ℝ => pairing (perturb m v a)
(perturb m v a))`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem pairing_perturb {ι : Type*} [Fintype ι] {v : ι → ℝ → ℝ} {m : ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (a : ι → ℝ) :
    pairing (perturb m v a) (perturb m v a)=pairing m m+
      (∑ i,a i*pairing (v i) m)+(∑ i,a i*pairing m (v i))+
      ∑ i,∑ j,a i*a j*pairing (v i) (v j) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let d := fun x => ∑ i,a i*v i x
  -- Establish hd as the integrability justification for the later integral estimates or
  -- changes of order.
  have hd : Integrable d := integrable_finsetSum _ (fun i _ => (hv i).const_mul (a i))
  change pairing (m+d) (m+d)=_
  rw [pairing_add_left hm hd (hm.add hd),pairing_add_right hm hm hd,pairing_add_right hd hm hd]
  have hl : pairing d m=∑ i,a i*pairing (v i) m := by
    rw [pairing_sum_left (fun i => (hv i).const_mul (a i)) hm]
    apply Finset.sum_congr rfl
    intro i _
    exact pairing_smul_left (a i) (v i) m
  have hr : pairing m d=∑ i,a i*pairing m (v i) := by
    rw [pairing_sum_right (fun i => (hv i).const_mul (a i)) hm]
    apply Finset.sum_congr rfl
    intro i _
    exact pairing_smul_right (a i) m (v i)
  have hdd : pairing d d=∑ i,∑ j,a i*a j*pairing (v i) (v j) := by
    rw [pairing_sum_left (fun i => (hv i).const_mul (a i)) hd]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairing_sum_right (fun j => (hv j).const_mul (a j)) ((hv i).const_mul (a i))]
    apply Finset.sum_congr rfl
    intro j _
    change pairing (a i • v i) (a j • v j)=_
    rw [pairing_smul_left,pairing_smul_right]
    ring
  rw [hl,hr,hdd]
  ring

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ (fun a : ι → ℝ => pairing (perturb m v a)
(perturb m v a))`.

Use: `«2610.05164v2».LocalObstruction.traceObservationWitness` uses this identity in the
displayed construction of `traceObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem pairing_finite_smooth {ι : Type*} [Fintype ι] {v : ι → ℝ → ℝ} {m : ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) :
    ContDiff ℝ ∞ (fun a : ι → ℝ => pairing (perturb m v a) (perturb m v a)) := by
  have he : (fun a : ι → ℝ => pairing (perturb m v a) (perturb m v a))=
      fun a => pairing m m+(∑ i,a i*pairing (v i) m)+(∑ i,a i*pairing m (v i))+
        ∑ i,∑ j,a i*a j*pairing (v i) (v j) := funext (pairing_perturb hm hv)
  rw [he]
  fun_prop

end
end «2610.05164v2».LocalObstruction
