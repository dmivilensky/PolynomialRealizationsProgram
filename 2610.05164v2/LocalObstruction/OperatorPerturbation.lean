import «2610.05164v2».LocalObstruction.FullResolvent
import Mathlib.Analysis.Analytic.Linear

/-!
Article: 2610.05164v2, Theorem 6.1.
Finite signed compact perturbations give a genuine polynomial family of full Sobolev pencils, with a
jointly analytic inverse near the positive base.
Use: `«2610.05164v2».LocalObstruction.densityOperator_perturb` feeds
`«2610.05164v2».LocalObstruction.fullPencil_joint_analytic` (full Pencil joint analytic).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open «2610.05164v2».Continuum MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `densityOperator (f+g)=densityOperator f+densityOperator g`.

Use: `«2610.05164v2».LocalObstruction.densityOperator_perturb` rewrites with this identity to
establish exact identity `densityOperator (perturb m v a)=densityOperator m+∑ i, a i •
densityOperator (v i)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.resolventGreen_density_derivative`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem densityOperator_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    densityOperator (f+g)=densityOperator f+densityOperator g := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  unfold densityOperator
  simp only [Pi.add_apply]
  have he : (fun x => (f x+g x) • featureProjection x)=
      fun x => f x • featureProjection x+g x • featureProjection x := by
    funext x
    module
  rw [he]
  exact integral_add (densityOperator_integrable hf) (densityOperator_integrable hg)

/--
Exact identity `densityOperator (a • f)=a • densityOperator f`.

Use: `«2610.05164v2».LocalObstruction.fullResolvent_density_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
fullResolvent (m+ε • v) s) (-((fullResolvent m s) ∘L ((s/2) • densityOperator v) ∘L
(fullResolvent m s))) 0`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.resolventGreen_density_derivative`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem densityOperator_smul (a : ℝ) (f : ℝ → ℝ) :
    densityOperator (a • f)=a • densityOperator f := by
  unfold densityOperator
  simp only [Pi.smul_apply,smul_eq_mul,mul_smul,integral_smul]

/--
Exact identity `densityOperator (perturb m v a)=densityOperator m+∑ i, a i • densityOperator (v
i)`.

Use: `«2610.05164v2».LocalObstruction.fullPencil_joint_analytic` rewrites with this identity to
establish the stated quantitative bound `AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ => fullPencil
(perturb m v z.1) z.2) p`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem densityOperator_perturb {ι : Type*} [Fintype ι] {m : ℝ → ℝ}
    {v : ι → ℝ → ℝ} (hm : Integrable m) (hv : ∀ i, Integrable (v i)) (a : ι → ℝ) :
    densityOperator (perturb m v a)=densityOperator m+∑ i, a i • densityOperator (v i) := by
  -- Establish hsum as the integrability justification for the later integral estimates or
  -- changes of order.
  have hsum : Integrable (fun x => ∑ i, a i*v i x) :=
    integrable_finsetSum _ (fun i _ => (hv i).const_mul (a i))

  change densityOperator (m+(fun x => ∑ i, a i*v i x))=_
  rw [densityOperator_add hm hsum]
  congr 1
  unfold densityOperator
  have he : (fun x => (∑ i, a i*v i x) • featureProjection x)=
      fun x => ∑ i, a i • (v i x • featureProjection x) := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    simp only [smul_apply, sum_apply]
    rw [Finset.sum_smul]
    simp only [smul_smul]
  rw [he]
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi (i : ι) : Integrable (fun x => a i • (v i x • featureProjection x)) := by
    convert! (densityOperator_integrable (hv i)).smul (a i) using 1
  rw [integral_finsetSum Finset.univ (f := fun i x => a i • (v i x • featureProjection x))
    (fun i _ => hi i)]
  simp only [integral_smul]


 /--
The stated quantitative bound `AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ => fullPencil (perturb m v
z.1) z.2) p`.

Use: `«2610.05164v2».LocalObstruction.fullResolvent_joint_analytic` uses this identity to
establish the stated quantitative bound `AnalyticAt ℝ (Ring.inverse ∘ (fun z : (ι → ℝ) × ℝ =>
fullPencil (perturb m v z.1) z.2)) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem fullPencil_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ}
    {v : ι → ℝ → ℝ} (hm : Integrable m) (hv : ∀ i, Integrable (v i))
    (p : (ι → ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ => fullPencil (perturb m v z.1) z.2) p := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun z : (ι → ℝ) × ℝ => fullPencil (perturb m v z.1) z.2)=
      fun z => ContinuousLinearMap.id ℝ FeatureSpace+
        (z.2/2) • (densityOperator m+∑ i, z.1 i • densityOperator (v i)) := by
    funext z
    rw [fullPencil,densityOperator_perturb hm hv]
  rw [he]
  apply analyticAt_const.add
  apply (analyticAt_snd.div_const (c := (2:ℝ))).smul
  apply analyticAt_const.add
  have hsum := Finset.analyticAt_sum Finset.univ (f := fun i (z : (ι → ℝ) × ℝ) =>
      z.1 i • densityOperator (v i)) (fun i _ =>
        (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt p.1).comp
          analyticAt_fst).smul analyticAt_const)
  convert! hsum using 1
  funext z
  simp only [Finset.sum_apply]

/--
The precise assertion is `AnalyticAt ℝ (Ring.inverse ∘ f) x`.

Use: `«2610.05164v2».LocalObstruction.fullResolvent_joint_analytic` uses this assertion to
establish the stated quantitative bound `AnalyticAt ℝ (Ring.inverse ∘ (fun z : (ι → ℝ) × ℝ =>
fullPencil (perturb m v z.1) z.2)) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Theorem 6.1.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem inverse_analytic_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → FeatureOperator} {x : E} (hf : AnalyticAt ℝ f x) (hu : IsUnit (f x)) :
    AnalyticAt ℝ (Ring.inverse ∘ f) x := by
  have hi : AnalyticAt ℝ Ring.inverse (f x) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hu.unit)
  exact hi.comp (f := f) hf

/--
The stated quantitative bound `AnalyticAt ℝ (Ring.inverse ∘ (fun z : (ι → ℝ) × ℝ => fullPencil
(perturb m v z.1) z.2)) ((0:ι → ℝ),s)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem fullResolvent_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ}
    {v : ι → ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x) (hv : ∀ i, Integrable (v i))
    {s : ℝ} (hs : 0≤s) :
    AnalyticAt ℝ (Ring.inverse ∘ (fun z : (ι → ℝ) × ℝ =>
      fullPencil (perturb m v z.1) z.2)) ((0:ι → ℝ),s) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply inverse_analytic_comp (fullPencil_joint_analytic hm hv ((0:ι → ℝ),s))
  have hz : perturb m v (0:ι → ℝ)=m := by funext x; simp [perturb]
  rw [hz]
  exact fullPencil_unit hm hn hs

end
end «2610.05164v2».LocalObstruction
