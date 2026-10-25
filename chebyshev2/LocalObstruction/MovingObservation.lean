import chebyshev2.LocalObstruction.ActualObservationWitnesses
import chebyshev2.LocalObstruction.MovingScaleCalculus

/-!
Article: chebyshev2, Theorem 6.1.
Moving scales introduce only another multiple of the proved ground-state gradient.
Use: `chebyshev2.LocalObstruction.movingObservationWitness` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.SineContinuum
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Exact identity `perturb m (fun _ : Fin 1 => v) (fun _ => ε)=m+ε • v`.

Use: `chebyshev2.LocalObstruction.movingObservationWitness` uses this identity in the
displayed construction of `movingObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem perturbFinOne_eq (m v : ℝ → ℝ) (ε : ℝ) :
    perturb m (fun _ : Fin 1 => v) (fun _ => ε)=m+ε • v := by
  funext x
  simp [perturb]

 /--
Constructs the object of type `ObservationWitness (fun f => R f (σ (groundCoupling f)))` and
discharges its required properties in the accompanying proof.

Use: `chebyshev2.LocalObstruction.ObservationSpec.witness` uses this definition in the
displayed construction of `ObservationSpec.witness`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
def movingObservationWitness (R : (ℝ → ℝ) → ℝ → ℝ) (σ : ℝ → ℝ)
    (hσ : ContDiffAt ℝ 1 σ (groundCoupling m))
    (W : ObservationWitness (fun f => R f (σ (groundCoupling m))))
    (hjoint : ∀ (d : ℕ) (v : Fin d → SmoothTest), ContDiffAt ℝ 1
      (fun p : (Fin d → ℝ) × ℝ => R (perturb m (fun i x => v i x) p.1) p.2)
      (0,σ (groundCoupling m))) :
    ObservationWitness (fun f => R f (σ (groundCoupling f))) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let s := σ (groundCoupling m)
  have hbase : ContDiffAt ℝ 1 (R m) s := by
    have hf := hjoint 0 (fun i => Fin.elim0 i)
    have ht := hf.comp s (contDiffAt_const.prodMk contDiffAt_id)
    convert! ht using 1
    funext t
    dsimp only [Function.comp_def]
    congr 1
    funext x
    simp [perturb]
  let c := deriv (R m) s*deriv σ (groundCoupling m)
  refine ⟨W.gradient.add (groundGradient.smul c),?_,?_⟩
  · intro h w
    let K := fun a : Fin 5 → ℝ => groundCoupling (perturb m (fun i x => curveBasis h w i x) a)
    have hk : K 0=groundCoupling m := by
      dsimp only [K]
      congr 1
      funext x
      simp [perturb]
    have hsigma : ContDiffAt ℝ 1 σ (K 0) := by rw [hk];exact hσ
    have hK := groundObservationWitness.regular h w
    have hmap : ContDiffAt ℝ 1 (fun a : Fin 5 → ℝ => (a,σ (K a))) 0 :=
      contDiffAt_id.prodMk (hsigma.comp 0 hK)
    have hf : ContDiffAt ℝ 1
        (fun p : (Fin 5 → ℝ) × ℝ => R (perturb m (fun i x => curveBasis h w i x) p.1) p.2)
        (0,σ (K 0)) := by rw [hk];exact hjoint 5 (curveBasis h w)
    exact hf.comp 0 hmap
  · intro v
    let K := fun ε : ℝ => groundCoupling (m+ε • (v:ℝ → ℝ))
    have hk : K 0=groundCoupling m := by dsimp only [K];simp
    have hsigma : HasDerivAt σ (deriv σ (groundCoupling m)) (K 0) := by
      rw [hk]
      exact (hσ.differentiableAt (by norm_num : (1:ℕ∞ω)≠0)).hasDerivAt
    have hg := groundObservationWitness.variation v
    have hf : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => R (m+p.1 • (v:ℝ → ℝ)) p.2) (0,s) := by
      have hh := hjoint 1 (fun _ => v)
      have hp : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ((fun _ : Fin 1 => p.1),p.2)) (0,s) := by fun_prop
      have ht := hh.comp (0,s) hp
      convert! ht using 1
      funext p
      dsimp only [Function.comp_def]
      rw [perturbFinOne_eq]
    have hq : HasDerivAt (fun ε : ℝ => R (m+ε • (v:ℝ → ℝ)) (σ (K 0)))
        (∫ x,v x*W.gradient.value x) 0 := by rw [hk];exact W.variation v
    have hb : HasDerivAt (fun t : ℝ => R (m+(0:ℝ) • (v:ℝ → ℝ)) t)
        (deriv (R m) s) (σ (K 0)) := by
      simpa only [hk,zero_smul,add_zero] using
        (hbase.differentiableAt (by norm_num : (1:ℕ∞ω)≠0)).hasDerivAt
    have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => R (m+p.1 • (v:ℝ → ℝ)) p.2) (0,σ (K 0)) := by
      rw [hk]
      exact hf.differentiableAt (by norm_num : (1:ℕ∞ω)≠0)
    have ht := moving_scale_derivative hF hg hsigma hq hb
    convert! ht using 1
    change (∫ x,v x*(W.gradient.value x+c*groundGradient.value x))=
      (∫ x,v x*W.gradient.value x)+deriv (R m) s*deriv σ (groundCoupling m)*(∫ x,v x*groundGradient.value x)
    have he : (fun x => v x*(W.gradient.value x+c*groundGradient.value x))=
        fun x => v x*W.gradient.value x+c*(v x*groundGradient.value x) := by funext x;ring
    rw [he,integral_add (test_integrable v W.gradient.continuous)
      ((test_integrable v groundGradient.continuous).const_mul c),integral_const_mul]

end
end chebyshev2.LocalObstruction
