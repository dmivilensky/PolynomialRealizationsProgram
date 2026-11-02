import krylov.Methods.NazarethObserved
import krylov.OneGradient.EvaluatedCorrection
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), genuine own-returned-gradient projection.
Use: connect the original literal observed correction to the actual diagonal
latest-information solve, with exact recorded chronological coordinates.
Source: true one-gradient records, genuine conjugate evaluated steps and
proved own-newly-returned versus final gradient pairing equality. -/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original recorded-gradient projection has its exact actual finite
newest-age coordinate sum for every genuine one-gradient execution.
Use: its numerator is the real own newly returned gradient, not a supplied
or substituted final gradient observation.
Article: main_krylov, prop:classical(b), Nazareth77 equation (16).
Proof: actual record and pair dictionaries give the two real finite arrays.
Their genuine zip pairs the same indices; finite list summation is exactly
the real finite coefficient sum, with its true returned-gradient index. -/
theorem recorded_projection_coordinates (method : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    recordedProjectionCorrection (oneGradientRun method A g k)=
      ∑ i : Fin k,(-inner ℝ (oneGradientStep method A g (k-1-i.val))
        (oneGradientGradient method A g (k-i.val))/
          inner ℝ (oneGradientStep method A g (k-1-i.val))
            (A (k-1-i.val) (oneGradientStep method A g (k-1-i.val)))) •
              oneGradientStep method A g (k-1-i.val) := by
  let f : Fin k → IterationRecord E := fun i => ⟨0,0,oneGradientStep method A g (k-1-i.val),
    oneGradientGradient method A g (k-1-i.val+1),[]⟩
  let p : Fin k → E × E := fun i => (oneGradientStep method A g (k-1-i.val),
    A (k-1-i.val) (oneGradientStep method A g (k-1-i.val)))
  have hf : (oneGradientRun method A g k).records=List.ofFn f := by
    rw [oneGradientRun_records,executedPairs_ofFn,List.map_ofFn]
    rfl
  have hp : (oneGradientRun method A g k).pairs=List.ofFn p := by
    rw [oneGradientRun_pairs_segmentOperators,executedPairs_ofFn]
  have hz : List.ofFn (fun i => (f i,p i))=(List.ofFn f).zip (List.ofFn p) := by
    apply List.zip_of_prod
    · rw [List.map_ofFn]
      rfl
    · rw [List.map_ofFn]
      rfl
  rw [recordedProjectionCorrection,hf,hp,← hz,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply,f,p]
  rw [show k-1-i.val+1=k-i.val by have := i.isLt;omega]

/-- On the real evaluated-launch transcript, the original own-returned-gradient
projection correction is exactly the genuine observed-model virtual correction.
Use: the original classical final correction and true predicted point use
the actual recorded numerator, with no added gradient query.
Article: main_krylov, prop:classical(b), Dixon75/Nazareth77 equation (16).
Proof: actual conjugate steps give a positive diagonal latest model. Its
true inverse coefficients are the negative real final-residual pairings over
the observed energies. The proved own-returned pairing equality replaces each
numerator, and the exact genuine record coordinates give the source correction. -/
theorem evaluated_recorded_projection (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k
    recordedProjectionCorrection H=virtualCorrection H.pairs H.gradient := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  let s := fun i : Fin k => oneGradientStep method (fun _ => Q) g (k-1-i.val)
  let y := fun i : Fin k => Q (s i)
  let c := fun i : Fin k => inner ℝ (s i) (y i)
  have hi (i : Fin k) : k-1-i.val<N := by have := i.isLt;omega
  have hc (i : Fin k) : c i≠0 := by
    have hs : s i≠0 := by
      rw [show s i=trial (oneGradientRun method (fun _ => Q) g (k-1-i.val)) • CG.direction Q g (k-1-i.val) from
        evaluated_launch_step trial Q hQ hpos g N hpre ht _ (hi i).le]
      exact smul_ne_zero (ht _ (hi i)) ((CG.invariant_line_pos Q hpos g _
        (CG.invariant Q hQ hpos g _ (fun j hj => hpre j (hj.trans (hi i)))) (hpre _ (hi i))).1)
    exact (hpos _ hs).ne'
  have hmodel : pairModel s y=diagonal c := by
    rw [show y=(fun i => Q (s i)) from rfl,pairModel_quadratic s Q hQ]
    ext i j
    by_cases hij : i=j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij]
      apply evaluated_launch_conjugate trial Q hQ hpos g N hpre ht _ _ (hi i) (hi j)
      intro he
      apply hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
  have hinv : (pairModel s y)⁻¹=diagonal (fun i => (c i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [hmodel,Matrix.diagonal_mul_diagonal]
    have he : (fun i => c i*(c i)⁻¹)=(1 : Fin k → ℝ) := funext (fun i => mul_inv_cancel₀ (hc i))
    rw [he]
    exact Matrix.diagonal_one
  have hcoord := (oneGradient_full_virtual_coordinates method (fun _ => Q) g k).1
  rw [selectedWindow_full] at hcoord
  change virtualCorrection H.pairs H.gradient=combine s (modelCoefficients s (pairModel s y) H.gradient) at hcoord
  change recordedProjectionCorrection H=virtualCorrection H.pairs H.gradient
  rw [hcoord]
  change recordedProjectionCorrection (oneGradientRun method (fun _ => Q) g k)=_
  rw [recorded_projection_coordinates]
  unfold combine modelCoefficients
  rw [hinv]
  apply Finset.sum_congr rfl
  intro i _
  change (-inner ℝ (s i) (oneGradientGradient method (fun _ => Q) g (k-i.val))/c i) • s i=
    (-(((diagonal (fun j => (c j)⁻¹))*ᵥ coordinates s H.gradient) i)) • s i
  rw [Matrix.mulVec_diagonal]
  have hpair := evaluated_step_returned_pairing trial Q hQ hpos g N hpre ht (k-1-i.val) k
    (by have := i.isLt;omega) hk
  have he : k-1-i.val+1=k-i.val := by have := i.isLt;omega
  rw [he] at hpair
  change (-inner ℝ (s i) (oneGradientGradient method (fun _ => Q) g (k-i.val))/c i) • s i=
    (-((c i)⁻¹*inner ℝ (s i) H.gradient)) • s i
  have hg : inner ℝ (s i) H.gradient=inner ℝ (s i) (oneGradientGradient method (fun _ => Q) g (k-i.val)) := hpair
  rw [hg]
  congr 1
  ring

end
end krylov.OneGradient
