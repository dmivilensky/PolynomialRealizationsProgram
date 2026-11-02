import krylov.Information.NaturalInner
import krylov.Information.CommonTwin

/-!
Article: main_krylov, s4:cor-Q, the actual common admissible pre-quadratic twin.
Use: primitive original inner slack produces one genuinely admissible
physical twin for every competing source method, with its own true base
displacement bounded in the original physical metric.
Source: derived exact H1--H3, real common CG direction rank, genuine
physical reflection budgets and zero intermediate correction defects.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The same concrete common pre-quadratic physical twin satisfies every original source admissibility constraint under exactly the stated primitive inner slack.
Use: the instance-comparison partner is an actual admissible physical source chosen independently of every competing method.
Article: main_krylov, s4:cor-Q, actual common admissible twin.
Proof: actual common CG rank justifies the physical coordinate inverse. The original inner slack derives every genuine H1--H3 reflection requirement, while exact forward form transport gives the real coordinate metric and primitive symmetries. Reuse the proved complete physical reflection budget theorem. The chosen genuine zero intermediate defects satisfy all remaining independent source budgets. -/
theorem Scenario.NaturalInner.commonTwin_admissible {S : Scenario (N+1)}
    {A Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef) (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    {r w τ : ℝ} {ω : ℕ → ℝ} (h : S.NaturalInner A r ω w τ)
    (hpre : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) (hr : 0≤r) (hw : 0≤w) (hτ : 0≤τ)
    (hsmall : 4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1) :
    (S.preQuadraticTwin Q g).Admissible N A r ω w τ := by
  -- Derive the true common coordinate metric and every original reflected source budget.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let C := S.inCoordinates D
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  have hC : C.base.PosDef := formMap_posDef D S.base hD h.original.1
  have hCE (i : ℕ) (hi : i<N) : (C.increment i).IsSymm := formMap_isSymm D _ (h.original.2.2.1 i hi).1
  have hCT : C.terminal.IsSymm := formMap_isSymm D _ h.original.2.2.2.1
  obtain ⟨he,hv,hH1,hH2,hH3,_⟩ := h.reflection_controls hA hQ hcount hpre hN hr hw hsmall
  have hω (i : ℕ) (hi : i<N) : 0≤ω i := (norm_nonneg (relativeOperator S.base (S.increment i))).trans (h.original.2.2.1 i hi).2
  have ht := C.physical_reflection_budgets N (formMap D A) D (formMap_posDef D A hD hA) hD hC he hCE hCT hv hr hw ω hω hH1 hH2 hH3
  rw [inverseFormMap_formMap D A hD] at ht
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,?_⟩
  intro i _
  refine ⟨Matrix.isSymm_zero,?_⟩
  change relativeBudget _ 0≤τ
  simpa only [relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero] using hτ


/-- The actual common admissible pre-quadratic twin changes the original physical base by relative spectral budget at most 4W₀.
Use: the genuine own-base risk and reference-error normalizations can be compared quantitatively.
Article: main_krylov, s4:cor-Q, actual common admissible twin.
Proof: the derived original common-coordinate reflection has actual base displacement at most its true hidden-base bound. Exact inverse form transport preserves that genuine relative budget, and the proved primitive inner slack bounds the original displacement by 4W₀. -/
theorem Scenario.NaturalInner.commonTwin_base_displacement {S : Scenario (N+1)}
    {A Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef) (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    {r w τ : ℝ} {ω : ℕ → ℝ} (h : S.NaturalInner A r ω w τ)
    (hpre : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) (hr : 0≤r) (hw : 0≤w)
    (hsmall : 4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1) :
    relativeBudget S.base ((S.preQuadraticTwin Q g).base-S.base)≤4*(∑ i∈range N, ω i) := by
  -- Derive the true common coordinate metric and every original reflected source budget.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let C := S.inCoordinates D
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  have hC : C.base.PosDef := formMap_posDef D S.base hD h.original.1
  have hCE (i : ℕ) (hi : i<N) : (C.increment i).IsSymm := formMap_isSymm D _ (h.original.2.2.1 i hi).1
  obtain ⟨he,_,_,_,_,hv4⟩ := h.reflection_controls hA hQ hcount hpre hN hr hw hsmall
  have hdisp := C.reflect_base_displacement N hC he hCE
  have hsym : ((C.reflect N).base-C.base).IsSymm :=
    (C.reflect_base_isSymm N hC.1.isSymm hCE).sub hC.1.isSymm
  have ht := (inverseForm_budget D C.base ((C.reflect N).base-C.base) hD hC hsym).le.trans hdisp
  have hb : inverseFormMap D C.base=S.base := inverseFormMap_formMap D S.base hD
  have hd : (S.preQuadraticTwin Q g).base-S.base=inverseFormMap D ((C.reflect N).base-C.base) := by
    change inverseFormMap D (C.reflect N).base-S.base=inverseFormMap D ((C.reflect N).base-C.base)
    rw [map_sub,hb]
  rw [hb,← hd] at ht
  exact ht.trans hv4

end
end krylov.Information

