import krylov.Convergence.WindowModelBounds
import krylov.Stability.AnalyticFC
import krylov.Stability.AnalyticMatrix
import krylov.Stability.CompactFirstOrder
import krylov.Correction.FullReconstruction
import krylov.Functions.FCReferenceFields
import krylov.Stability.CompactEventual
import krylov.Methods.HomogeneousFC

/-!
Article: main_krylov, thm:D, extra corrections with the frozen full model.
Use: form the actual latest-information ambient matrix from the complete
executed FC window, prove its exact quadratic value, and establish genuine
analyticity before substituting actual scalar-function secants.
Source: genuine adaptive FC regularity, full CG independence, and the
symmetric multipoint secant model of Burdakov (1983).
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Correction
  krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The chronological full observed FC step window. Article: thm:D. -/
def fcFrozenColumns (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i=>fcStep fullMemory A g i.val

/-- The genuine ambient matrix of the latest-information model of all
executed FC pairs. Article: main_krylov, thm:D, frozen final corrections. -/
def fcFrozenMatrix (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  inverseCongruence (windowMatrix (fcFrozenColumns A g))
    (ss1Model (fcFrozenColumns A g) (fun i=>A i.val (fcFrozenColumns A g i)))

/-- The full ambient model is unchanged by arbitrary invertible
rescaling of the actual observed columns. Article: thm:D. -/
theorem frozen_model_rescale
    (s y : Fin n → EuclideanSpace ℝ (Fin n)) (d : Fin n → ℝ)
    (hd : IsUnit (diagonal d).det) :
    inverseCongruence (windowMatrix (rescaleWindow s d))
      (ss1Model (rescaleWindow s d) (rescaleWindow y d))=
      inverseCongruence (windowMatrix s) (ss1Model s y) := by
  have hv : windowMatrix (rescaleWindow s d)=windowMatrix s*diagonal d := by
    ext i j
    simp only [windowMatrix,rescaleWindow,PiLp.smul_apply,smul_eq_mul,mul_diagonal]
    ring
  rw [hv,ss1Model_rescale]
  simp only [inverseCongruence,rescaleModel,transpose_mul,diagonal_transpose,Matrix.mul_inv_rev]
  have he : (windowMatrix s)ᵀ⁻¹*(diagonal d)⁻¹*(diagonal d*ss1Model s y*diagonal d)*
      ((diagonal d)⁻¹*(windowMatrix s)⁻¹)=
      (windowMatrix s)ᵀ⁻¹*((diagonal d)⁻¹*diagonal d)*ss1Model s y*
        (diagonal d*(diagonal d)⁻¹)*(windowMatrix s)⁻¹ := by noncomm_ring
  rw [he,nonsing_inv_mul _ hd,mul_nonsing_inv _ hd]
  simp only [Matrix.mul_one]

/-- The genuinely executed FC model is degree zero in its initial
gradient, including the totalized singular branches. Article: thm:D. -/
theorem fcFrozenMatrix_scalar
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) :
    fcFrozenMatrix A (c • g)=fcFrozenMatrix A g := by
  have hs : fcFrozenColumns A (c • g)=rescaleWindow (fcFrozenColumns A g) (fun _=>c) :=
    funext fun i=>(fullFC_scalar A g c hc n).2 i.val i.isLt |>.2
  have hy : (fun i : Fin n=>A i.val (fcFrozenColumns A (c • g) i))=
      rescaleWindow (fun i=>A i.val (fcFrozenColumns A g i)) (fun _=>c) := by
    funext i
    rw [hs]
    exact map_smul _ _ _
  unfold fcFrozenMatrix
  rw [hy,hs]
  exact frozen_model_rescale _ _ _ (by
    rw [det_diagonal,isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _=>hc))

/-- Only the complete measured finite operator prefix enters the frozen
FC model; no unused future operator is read. Article: thm:D. -/
theorem fcFrozenMatrix_congr_prefix
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hAB : ∀ i<n,A i=B i) :
    fcFrozenMatrix A g=fcFrozenMatrix B g := by
  have hs : fcFrozenColumns A g=fcFrozenColumns B g :=
    funext fun i=>fcStep_congr_operator_prefix A B g n i.val i.isLt hAB
  unfold fcFrozenMatrix
  rw [hs]
  congr 2
  funext i
  rw [hAB i.val i.isLt]

/-- A full nonstagnating quadratic FC run supplies a genuine independent
ambient basis, derived from CG rather than required of the measured model.
Article: thm:D, full-cycle model domain. -/
theorem fcFrozenColumns_reference_independent
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin n)) (hpre : ∀ i<n,CG.gradient Q g i≠0) :
    LinearIndependent ℝ (fcFrozenColumns (fun _=>Q) g) := by
  have hs : fcFrozenColumns (fun _=>Q) g=(fun i : Fin n=>referenceStep Q g i.val) :=
    funext fun i=>(fullFC_reference_step Q hQ hpos g i.val).2.2
  rw [hs]
  exact reference_window_independent Q hQ hpos g n hpre
    (fun i : Fin n=>i.val) (fun i j hij=>Fin.ext hij) (fun i=>i.isLt)

/-- A compatible positive quadratic source is reconstructed exactly by
the actual frozen full latest-information model. Article: thm:D. -/
theorem fcFrozenMatrix_reference (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0) :
    fcFrozenMatrix (fun _=>cgOperator base) g=base := by
  let s := fcFrozenColumns (fun _=>cgOperator base) g
  let V := windowMatrix s
  have hV : IsUnit V.det := by
    exact fullBasisMatrix_unit s (fcFrozenColumns_reference_independent _
      (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g hpre)
  have hy : windowMatrix (fun i : Fin n=>cgOperator base (s i))=base*V := by
    ext a i
    change ((Matrix.toEuclideanCLM (𝕜:=ℝ) base) (s i)) a=∑ j,base a j*s i j
    conv_lhs => rw [←WithLp.toLp_ofLp 2 (s i),Matrix.toEuclideanCLM_toLp]
    rfl
  have hc : (Vᵀ*base*V).IsSymm := by
    simp only [Matrix.IsSymm,transpose_mul,transpose_transpose,hb.1.isSymm.eq,Matrix.mul_assoc]
  change inverseCongruence V (ss1Model s (fun i=>cgOperator base (s i)))=base
  rw [ss1Model,crossGram_windowMatrix,hy,←Matrix.mul_assoc,latest_eq_of_isSymm hc]
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  simp only [inverseCongruence,←Matrix.mul_assoc,nonsing_inv_mul _ ht,Matrix.one_mul]
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hV,Matrix.mul_one]

/-- The true frozen full model is jointly analytic at every genuine
nonstagnating quadratic source. No inverse or model regularity is assumed.
Article: main_krylov, thm:D and lem:U. -/
theorem fcFrozenMatrix_analyticAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X)
    (hA : ∀ i,AnalyticAt ℝ (fun z=>A z i) x) (hg : AnalyticAt ℝ g x)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hAx : A x=fun _=>Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v)) (hpre : ∀ i<n,CG.gradient Q (g x) i≠0) :
    AnalyticAt ℝ (fun z=>fcFrozenMatrix (A z) (g z)) x := by
  have hp := quadraticFC_prefix_analytic A g x hA hg Q hAx hQ hpos n hpre
  let s := fun z=>fcFrozenColumns (A z) (g z)
  let V := fun z=>windowMatrix (s z)
  have hs (i : Fin n) : AnalyticAt ℝ (fun z=>s z i) x := (hp.2 i.val i.isLt).2
  have hV (i j : Fin n) : AnalyticAt ℝ (fun z=>V z i j) x :=
    ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n=>ℝ) i).analyticAt _).comp (hs j)
  have hu : IsUnit (V x).det := by
    change IsUnit (fullBasisMatrix (s x)).det
    apply fullBasisMatrix_unit
    change LinearIndependent ℝ (fcFrozenColumns (A x) (g x))
    rw [hAx]
    exact fcFrozenColumns_reference_independent Q hQ hpos (g x) hpre
  have hi := analytic_spectral_matrix_inv V x hV (isUnit_iff_ne_zero.mp hu)
  have hit := analytic_spectral_matrix (fun z=>(V z)ᵀ⁻¹) x
    (fun i j=>analytic_matrix_inv (fun z=>(V z)ᵀ) x (fun a b=>hV b a)
      (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hu) i j)
  have hM := analytic_spectral_matrix (fun z=>ss1Model (s z)
      (fun i=>A z i.val (s z i))) x (fun i j=>
        analytic_inner (hs (min i j))
          (analytic_operator_apply (hA (max i j).val) (hs (max i j))))
  exact (hit.mul hM).mul hi

/-- One common first-order tube controls the actual frozen full model
before every compact family of full nonstagnating references.
Article: main_krylov, thm:D. The only perturbations are the independent
finite operator inputs and initial observed gradient of the real FC run. -/
theorem compact_fcFrozenMatrix_first_order
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<n,CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ,0<δ ∧0<C ∧∀ g∈K,∀ v : EuclideanSpace ℝ (Fin n),
      ∀ Θ : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ‖(v,Θ)‖≤δ →
      ‖fcFrozenMatrix (fcFiniteOperatorPath (cgOperator base) n Θ) (g+v)-base‖≤C*‖(v,Θ)‖ := by
  let F := fun z : EuclideanSpace ℝ (Fin n) ×
      (Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))=>
    fcFrozenMatrix (fcFiniteOperatorPath (cgOperator base) n z.2) z.1
  have hF g (hg : g∈K) : AnalyticAt ℝ F (g,0) :=
    fcFrozenMatrix_analyticAt _ Prod.fst (g,0)
      (fun i=>fcFiniteOperatorPath_analytic _ n i (g,0)) analyticAt_fst _
      (fcFiniteOperatorPath_zero _ n) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 (hpre g hg)
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F K hK hF
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg v Θ hΘ
  have hh := hbound g hg v Θ hΘ
  dsimp only [F] at hh
  rwa [fcFiniteOperatorPath_zero,fcFrozenMatrix_reference base hb g (hpre g hg)] at hh

/-- The actual complete column basis and the actual frozen model inverse
are uniformly defined and bounded on one compact source tube.
Article: thm:D. All inverse domains come from the true full CG basis. -/
theorem compact_fcFrozenMatrix_domains
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<n,CG.gradient (cgOperator base) g i≠0) :
    ∃ δ B : ℝ,0<δ ∧0<B ∧∀ g∈K,∀ v : EuclideanSpace ℝ (Fin n),
      ∀ Θ : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ‖(v,Θ)‖≤δ →
      let A := fcFiniteOperatorPath (cgOperator base) n Θ
      IsUnit (windowMatrix (fcFrozenColumns A (g+v))).det ∧
        IsUnit (fcFrozenMatrix A (g+v)).det ∧‖(fcFrozenMatrix A (g+v))⁻¹‖≤B := by
  let A := fun z : EuclideanSpace ℝ (Fin n) ×
      (Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))=>
    fcFiniteOperatorPath (cgOperator base) n z.2
  let F := fun z=>fcFrozenMatrix (A z) z.1
  let V := fun z=>windowMatrix (fcFrozenColumns (A z) z.1)
  have hF g (hg : g∈K) : AnalyticAt ℝ F (g,0) :=
    fcFrozenMatrix_analyticAt A Prod.fst (g,0)
      (fun i=>fcFiniteOperatorPath_analytic _ n i (g,0)) analyticAt_fst _
      (fcFiniteOperatorPath_zero _ n) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 (hpre g hg)
  have hFzero g (hg : g∈K) : F (g,0)=base := by
    dsimp only [F,A]
    rw [fcFiniteOperatorPath_zero,fcFrozenMatrix_reference base hb g (hpre g hg)]
  have hV g (hg : g∈K) : AnalyticAt ℝ V (g,0) := by
    have hp := quadraticFC_prefix_analytic A Prod.fst (g,0)
      (fun i=>fcFiniteOperatorPath_analytic _ n i (g,0)) analyticAt_fst _
      (fcFiniteOperatorPath_zero _ n) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 n (hpre g hg)
    apply analytic_spectral_matrix
    intro i j
    exact ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n=>ℝ) i).analyticAt _).comp (hp.2 j.val j.isLt).2
  have hu g (hg : g∈K) : IsUnit (V (g,0)).det := by
    change IsUnit (fullBasisMatrix (fcFrozenColumns
      (fcFiniteOperatorPath (cgOperator base) n 0) g)).det
    rw [fcFiniteOperatorPath_zero]
    exact fullBasisMatrix_unit _ (fcFrozenColumns_reference_independent _
      (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g (hpre g hg))
  have hfentry g (hg : g∈K) (i j : Fin n) : AnalyticAt ℝ (fun z=>F z i j) (g,0) :=
    ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin n × Fin n=>ℝ) (i,j)).analyticAt _).comp
      (((matrixEntryEquiv n n).analyticAt _).comp (hF g hg))
  have hventry g (hg : g∈K) (i j : Fin n) : AnalyticAt ℝ (fun z=>V z i j) (g,0) :=
    ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin n × Fin n=>ℝ) (i,j)).analyticAt _).comp
      (((matrixEntryEquiv n n).analyticAt _).comp (hV g hg))
  obtain ⟨ed,hed,hd⟩ := compact_reference_eventual_tube
    (fun z=>IsUnit (V z).det ∧IsUnit (F z).det) K hK (fun g hg=>by
      have hv := (analytic_matrix_det V (g,0) (hventry g hg)).continuousAt.eventually_ne
        (isUnit_iff_ne_zero.mp (hu g hg))
      have hf := (analytic_matrix_det F (g,0) (hfentry g hg)).continuousAt.eventually_ne
        (by rw [hFzero g hg]; exact hb.det_pos.ne')
      filter_upwards [hv,hf] with z hz hfz
      exact ⟨isUnit_iff_ne_zero.mpr hz,isUnit_iff_ne_zero.mpr hfz⟩)
  have hi g (hg : g∈K) : AnalyticAt ℝ (fun z=>(F z)⁻¹) (g,0) :=
    analytic_spectral_matrix_inv F (g,0) (hfentry g hg)
      (by rw [hFzero g hg]; exact hb.det_pos.ne')
  obtain ⟨eb,B,heb,hB,hbound⟩ := compact_reference_value_tube (fun z=>(F z)⁻¹) K hK hi
  refine ⟨min ed eb,B,by positivity,hB,?_⟩
  intro g hg v Θ hΘ
  exact ⟨(hd g hg v Θ (hΘ.trans (min_le_left _ _))).1,
    (hd g hg v Θ (hΘ.trans (min_le_left _ _))).2,
    hbound g hg v Θ (hΘ.trans (min_le_right _ _))⟩

end
end krylov.Convergence
