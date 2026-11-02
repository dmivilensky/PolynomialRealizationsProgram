import krylov.Completion.ObservedWindowEstimate
import krylov.Methods.VirtualReference
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, genuine quadratic observed-window domains.
Use: derive physical completion feasibility for actual DC and XRFC observed
directions from their original independent quadratic secants.
Source: genuine positive conjugacy Gram, real native direction orthogonality
and the actual physical matrix/operator coordinates.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.Reference krylov.Methods
variable {n : ℕ}

/-- An independent genuine quadratic observed window and its nonzero native
conjugate direction have every physical window-completion domain.
Use: both DC and XRFC policies obtain rank, a new direction and a feasible
physical completion from actual observations, without supplied certificates.
Article: main_krylov, thm:radau and cor:quant(a).
Proof: true quadratic secants make the actual conjugacy Gram positive. The
native direction annihilates all old images; positive definiteness therefore
keeps its nonzero vector outside the old span. Original physical coordinates
give exactly the observed model and conjugacy constraints. -/
theorem quadratic_observed_window_feasible (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n))
    (hy : ∀ j,windowImages W j=cgOperator base (windowSteps W j))
    (hLI : LinearIndependent ℝ (windowSteps W)) (hd : windowDirection W g≠0) :
    let S : Matrix (Fin n) (Fin W.length) ℝ := fun i j => windowSteps W j i
    let d := WithLp.ofLp (windowDirection W g)
    Function.Injective S.mulVec ∧ d∉LinearMap.range S.mulVecLin ∧
      base∈windowCurvatureCompletions S d (windowModel W) mu upper := by
  let s := windowSteps W
  let Q := cgOperator base
  let d := windowDirection W g
  let S : Matrix (Fin n) (Fin W.length) ℝ := fun i j => s j i
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hY : windowImages W=fun j => Q (s j) := funext hy
  have hu : IsUnit (crossGram (windowImages W) s).det := by
    rw [hY]
    exact isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hLI).det_pos.ne'
  have horth (j : Fin W.length) : inner ℝ (s j) (Q d)=0 := by
    have h := congrFun (conjugacyDirection_conjugate s (windowImages W) g hu) j
    change inner ℝ (windowImages W j) d=0 at h
    rw [hy j] at h
    exact (hQ (s j) d).symm.trans h
  have hS : Function.Injective S.mulVec := Matrix.mulVec_injective_iff.mpr
    (hLI.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).ker)
  have hnew : WithLp.ofLp d∉LinearMap.range S.mulVecLin := by
    rintro ⟨c,hc⟩
    have he : combine s c=d := by
      ext i
      have hi := congrFun hc i
      change (S*ᵥ c) i=d i at hi
      simpa only [combine,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
        Matrix.mulVec,dotProduct,S,s,mul_comm] using hi
    have hmem : d∈Submodule.span ℝ (Set.range s) := he ▸ combine_mem_span s c
    have hker : Submodule.span ℝ (Set.range s)≤(innerSL ℝ (Q d)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change inner ℝ (Q d) (s j)=0
      rw [real_inner_comm]
      exact horth j
    have hz := hker hmem
    change inner ℝ (Q d) d=0 at hz
    rw [real_inner_comm] at hz
    exact (hpos d hd).ne' hz
  refine ⟨hS,hnew,hb.1.isSymm,hlo,hhi,?_,?_⟩
  · rw [windowModel_quadratic W Q hQ hy]
    ext i j
    change (Sᵀ*base*S) i j=inner ℝ (Q (s i)) (s j)
    have hs : inner ℝ (Q (s i)) (s j)=inner ℝ (s i) (Q (s j)) := hQ (s i) (s j)
    rw [hs]
    change _=inner ℝ (s i) (cgOperator base (s j))
    rw [cgOperator,Matrix.inner_toEuclideanCLM,Matrix.mul_assoc]
    rfl
  · ext j
    change (s j).ofLp ⬝ᵥ (base*ᵥ d.ofLp)=0
    simpa only [Q,cgOperator,Matrix.inner_toEuclideanCLM,star_trivial] using horth j

end
end krylov.Completion
