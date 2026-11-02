import krylov.Convergence.OrderDeferredTensor
import krylov.Convergence.OrderDeferredConstant
import krylov.Convergence.OrderSchurHistory
import krylov.Convergence.OrderGradientErrorTransfer
import krylov.Functions.NativeRFCFPhysicalTransfer
import krylov.Cancellation.DeferredSchurSharp

/-!
Article: main_krylov, thm:D, literal data-based DC sharp cycle error.
Use: the actual observed Schur arithmetic rule has the printed Chebyshev
constant, with no estimate homogeneity, chart, positivity or output-bound
premise. True source geometry derives every execution and error estimate.
Source: genuine scalar search-only transfer, actual Schur reference data,
compatible third-derivative response and gradient/error normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The original implemented Schur data-midpoint DC cycle has the exact
printed leading true-metric error constant. Article: thm:D and thm:DC. -/
theorem nativeDC_sharp_error
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (K : Set E) (hK : IsCompact K) (hcount : ∀ g∈K,referenceAtomCount base hb g=k+1)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖u‖≤B → cgOperator base u∈K →
      ‖cgOperator (metricRoot base) u‖=1 →
      ‖metricCoordinates base hb (scalarFunctionPoint (deferredDataMethod fullMemory (k+1)
          (dcSchurGaussRadauEstimate fullMemory mu upper)) (metricCoordinates base hb) f G r (ε • u) (k+1))‖≤
        (m*dcRestartConstant (designSpacing I) ((upper-mu)/(upper+mu)) k+η)*ε^2 := by
  let estimate : History E → ℝ:=dcSchurGaussRadauEstimate fullMemory mu upper
  let method:=deferredDataMethod fullMemory (k+1) estimate
  let Q:=cgOperator base
  let C₀:=m*dcRestartConstant (designSpacing I) ((upper-mu)/(upper+mu)) k
  let admission:=fun u : E=>‖u‖≤B ∧Q u∈K ∧‖cgOperator (metricRoot base) u‖=1
  let point:=fun (ε : ℝ) (u : E)=>scalarFunctionPoint method (metricCoordinates base hb) f G r (ε • u) (k+1)
  have hpre : ∀ g∈K,∀ i<k+1,CG.gradient Q g i≠0 :=
    fun g hg i hi=>cg_nonstagnation base hb g i (by rw [hcount g hg];exact hi)
  have hdata g (hg : g∈K):=deferred_schur_reference_data fullMemory (fun _ hj=>hj) (k+1)
    base hb mu upper hmu hmuL hlo hhi g k (hpre g hg) 2
  have hhom : method.Homogeneous:=deferredSchurMethod_homogeneous fullMemory (k+1) mu upper
  have hconsistent : CGConsistent method:=deferred_data_consistent fullMemory (fun _ hj=>hj) (k+1) estimate
  have hp:=cgOperator_positive base hb
  have hs g (hg : g∈K) : SmoothProbedCycleAt method 2 Q g (k+1):=
    deferred_schur_smoothCycleAt fullMemory (fun _ hj=>hj) (k+1) base hb mu upper hmu hmuL hlo hhi
      g (k+1) (hpre g hg) 2
  have hpoint : ∃ ep M : ℝ,0<ep ∧0<M ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤M*ε^2 := by
    obtain ⟨ep,C,hep,hC,hbound⟩:=scalarSearchOnlyPoint_reference_points method (fun _ _=>rfl)
      hconsistent hhom (metricCoordinates base hb) (metricCoordinates_inverse_symmetric base hb)
      f G H Q hr hG₀ hH₀ (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG
      hp.1 hp.2 (k+1) K hK hpre hs B hB
    refine ⟨ep,‖(metricCoordinates base hb).toContinuousLinearMap‖*C+1,hep,by positivity,?_⟩
    intro ε hε he u hu
    have hh:=hbound ε hε he u hu.1 hu.2.1 (k+1) le_rfl
    rw [fcQuadraticReferencePoint_full_zero base hb,smul_zero,sub_zero] at hh
    have hn:=((metricCoordinates base hb).toContinuousLinearMap.le_opNorm (point ε u)).trans
      (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    exact hn.trans (by nlinarith only [sq_nonneg ε])
  have hρ : 0≤(upper-mu)/(upper+mu):=div_nonneg (sub_nonneg.mpr hmuL) (by linarith)
  have hρ1 : (upper-mu)/(upper+mu)≤1 := by
    apply (div_le_one (by linarith : 0<upper+mu)).mpr
    linarith
  have hgradient : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,admission u →
      ‖cgOperator (metricRoot base)⁻¹ (G (point ε u))‖≤(C₀+η)*ε^2 := by
    intro η hη
    obtain ⟨ep,hep,hbound⟩:=deferredFunctionPoint_spatial_leading_gradient estimate hhom base hb k rfl
      f G H D hD hr hG₀ hH₀ hLr hH hF hG K hK hcount (fun g hg=>(hdata g hg).2.1)
      (fun g hg=>(hdata g hg).1) B hB η hη
    refine ⟨ep,hep,?_⟩
    intro ε hε he u hu
    have hrem:=hbound ε hε he u hu.1 hu.2.1
    have hdamp:=deferred_schur_reference_damping fullMemory (fun _ hj=>hj) (k+1)
      base hb mu upper hmu hmuL hlo hhi (Q u) k (hpre _ hu.2.1)
    let a₀:=estimate (methodRun method (fun _=>Q) (fun _=>Q) (Q u) k)
    have hcoef:=dc_spatial_tensor_restart_constant I base hb D T hT m hm hdiag hband u
      (hcount _ hu.2.1) hu.2.2 (1-CG.length Q (Q u) k/a₀) _ hρ hρ1 hdamp.2
    have hn:=norm_le_norm_sub_add (cgOperator (metricRoot base)⁻¹ (G (point ε u)))
      (ε^2 • deferredResponse base (Q u) k (1-CG.length Q (Q u) k/a₀) (fcCompatibleIncrements base hb D u))
    rw [norm_smul,Real.norm_of_nonneg (sq_nonneg ε)] at hn
    exact hn.trans ((add_le_add hrem (mul_le_mul_of_nonneg_left hcoef (sq_nonneg ε))).trans_eq (by dsimp only [C₀];ring))
  have htransfer:=actual_metric_error_of_gradient_asymptotic base hb G H hr hG₀ hH₀ hH hG
    point admission 2 (Or.inl rfl) C₀ hpoint hgradient
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=htransfer η hη
  exact ⟨ep,hep,fun ε hε he u hu hKu hunit=>hbound ε hε he u ⟨hu,hKu,hunit⟩⟩

end
end krylov.Convergence
