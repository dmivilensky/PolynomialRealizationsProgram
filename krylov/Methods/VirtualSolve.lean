import krylov.Methods.OneGradient
import krylov.Methods.ReferenceModels

/-!
Article: main_krylov, lem:consistent(b,c), actual virtual Galerkin solves.
Use: characterize the computed virtual displacement by its observed-span and
Galerkin equations, then connect extrapolated gradients to real quadratic gradients.
Source: uniqueness of a positive quadratic minimizer on an independent finite window.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Actual operator application commutes with the finite physical window combination.
Use: true quadratic secants make model extrapolation equal the actual gradient change.
Article: main_krylov, lem:consistent(b,c), Yw=ASw.
Proof: move the continuous linear operator through the genuine finite sum and scalar multiples. -/
theorem combine_operator (Q : E →L[ℝ] E) (s : ι → E) (c : ι → ℝ) :
    Q (combine s c)=combine (fun i => Q (s i)) c := by
  simp only [combine, map_sum, map_smul]

omit [Fintype ι] in
/-- A symmetric physical operator transfers between the two actual coordinate pairings.
Use: model normal equations use the same true positive operator Gram matrix in either orientation.
Article: main_krylov, lem:consistent, SᵀAv=(AS)ᵀv.
Proof: apply actual operator symmetry to each finite coordinate. -/
theorem coordinates_operator (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (s : ι → E) (v : E) :
    coordinates s (Q v)=coordinates (fun i => Q (s i)) v := by
  ext i
  exact (hQ (s i) v).symm

variable [DecidableEq ι]

/-- The computed finite model correction equals every stored-span candidate satisfying its actual normal equations.
Use: virtual CG consistency follows from genuine computed model coefficients, not an assumed projection output.
Article: main_krylov, lem:consistent(b,c), Galerkin model minimizer.
Proof: represent the candidate in the actual independent stored family; its
Galerkin equation solves the same nonsingular matrix system as the implemented inverse. -/
theorem modelCorrection_unique (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (s : ι → E) (g u : E) (hC : IsUnit (crossGram (fun i => Q (s i)) s).det)
    (hu : u∈Submodule.span ℝ (Set.range s)) (ho : coordinates s (g+Q u)=0) :
    combine s (modelCoefficients s (crossGram (fun i => Q (s i)) s) g)=u := by
  -- The candidate's actual physical coordinates determine its computed model coefficient vector uniquely.
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  change combine s c=u at hc
  have he : crossGram (fun i => Q (s i)) s *ᵥ c= -coordinates s g := by
    rw [← coordinates_combine, ← coordinates_operator Q hQ, hc]
    ext i
    have hz := congrFun ho i
    change inner ℝ (s i) (g+Q u)=0 at hz
    change inner ℝ (s i) (Q u)= -inner ℝ (s i) g
    rw [inner_add_right] at hz
    linarith
  have hw : modelCoefficients s (crossGram (fun i => Q (s i)) s) g=c := by
    rw [modelCoefficients, ← Matrix.mulVec_neg, ← he, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hC, Matrix.one_mulVec]
  rw [hw, hc]

/-- True quadratic observations make the actually extrapolated virtual gradient the actual output gradient.
Use: the policy computes no hidden operator action when forming its virtual gradient.
Article: main_krylov, lem:consistent(b,c), ĝ=g+ASw.
Proof: replace each genuinely observed image by its true quadratic image and commute the actual finite combination with the operator. -/
theorem virtualGradient_quadratic (W : List (E × E)) (Q : E →L[ℝ] E) (g : E)
    (hy : ∀ i, windowImages W i=Q (windowSteps W i)) :
    virtualGradient W g=g+Q (virtualCorrection W g) := by
  rw [virtualGradient, virtualCorrection, combine_operator]
  congr 2
  exact funext hy

/-- The computed virtual displacement is exactly any actual stored-span quadratic Galerkin correction.
Use: a single genuine solve theorem covers both step and direction bases.
Article: main_krylov, lem:consistent(b,c), virtual correction.
Proof: the actual latest model equals its true positive Gram matrix; the
stored-family independence makes it nonsingular, and the proved computed normal-equation uniqueness applies. -/
theorem virtualCorrection_unique (W : List (E × E)) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hy : ∀ i, windowImages W i=Q (windowSteps W i)) (hs : LinearIndependent ℝ (windowSteps W))
    (g u : E) (hu : u∈Submodule.span ℝ (Set.range (windowSteps W)))
    (ho : coordinates (windowSteps W) (g+Q u)=0) : virtualCorrection W g=u := by
  unfold virtualCorrection virtualCoefficients
  rw [windowModel_quadratic W Q hQ hy]
  exact modelCorrection_unique Q hQ _ g u
    (isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hs).det_pos.ne') hu ho

/-- Every genuinely observed pair of a static one-gradient run has its true quadratic operator image.
Use: actual XRFC windows have Y=AS by executed observations, independently of consistency.
Article: main_krylov, lem:consistent(b), quadratic observed pairs.
Proof: induct on actual evaluated queries; the new gradient difference is Qs,
and all earlier actual observed pairs are preserved in the actual stored history. -/
theorem oneGradientRun_pairs_quadratic (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    ∀ p∈(oneGradientRun m (fun _ => Q) g k).pairs, p.2=Q p.1 := by
  -- The proof uses actual oracle updates and never presumes a virtual trajectory.
  induction k with
  | zero => simp only [oneGradientRun, History.pairs, recordPairs, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | succ k ih =>
    intro p hp
    let H := oneGradientRun m (fun _ => Q) g k
    change p∈(m.step H,H.gradient+Q (m.step H)-H.gradient)::H.pairs at hp
    rw [add_sub_cancel_left] at hp
    rcases List.mem_cons.mp hp with he | he
    · rw [he]
    · exact ih p he

/-- A real static one-gradient query records its actual step and its true quadratic image.
Use: extend the stored-basis invariant through the actual algorithmic execution.
Article: main_krylov, lem:consistent(b,c), actual appended pair.
Proof: subtract the actual preceding gradient from the actual new oracle gradient. -/
theorem oneGradientRun_pairs_succ (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m (fun _ => Q) g (k+1)).pairs=
      (m.step (oneGradientRun m (fun _ => Q) g k), Q (m.step (oneGradientRun m (fun _ => Q) g k)))::
        (oneGradientRun m (fun _ => Q) g k).pairs := by
  let H := oneGradientRun m (fun _ => Q) g k
  change (m.step H,H.gradient+Q (m.step H)-H.gradient)::H.pairs=_
  rw [add_sub_cancel_left]

end
end krylov.Methods
