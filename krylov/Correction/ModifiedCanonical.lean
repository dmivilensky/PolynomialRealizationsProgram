import krylov.Correction.ModifiedExpansion
import krylov.Correction.CanonicalExpansion

/-!
Article: main_krylov, apD:lem-model, the actual canonical last-model change.
Use: identify the native physical model replacement with its exact canonical
inverse-congruence factor, before specializing to informed diagonal changes.
Source: the proved genuine full reference Gram and incoming-vector identities,
actual positive-root cancellation and the full modified physical cubic remainder.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Any actual native model change has precisely its canonical inverse-congruence action on the genuine fresh defect.
Use: the modified-model geometric coefficient is derived from the real stored basis, including its true head direction scale.
Article: main_krylov, apD:lem-model, Δ̂=V₀^(−T)Δ_H V₀^(−1).
Proof: recover the change from its exact full canonical congruence. The
actual reference Gram and incoming vector cancel the physical basis and
metric factors by the already proved full-reference coefficient identity. -/
theorem native_model_change_canonical {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
    let U := referenceModelBasis base g k
    let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
    let R := fullBasisMatrix U
    let V := metricRoot base*R
    cgOperator (metricRoot base)⁻¹
      (cgOperator (Rᵀ⁻¹*(D*H⁻¹)) (frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k))=
      ‖canonicalCGStep base g k‖ • cgOperator (inverseCongruence V D) (freshDefect base g E (k+1)) := by
  -- Derive the true reference basis inverse before transporting this arbitrary model change.
  let U := referenceModelBasis base g k
  let R := fullBasisMatrix U
  let V := metricRoot base*R
  let S := inverseCongruence V D
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ U := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g k hpre
  have hR : IsUnit R.det := fullBasisMatrix_unit _ hU
  have hV : IsUnit V.det := by
    change IsUnit (metricRoot base*R).det
    rw [det_mul]
    exact (metricRoot_det_unit base hb).mul hR
  have hD : D=Rᵀ*metricRoot base*S*metricRoot base*R := by
    simpa only [V,transpose_mul,(metricRoot_isSymm base).eq,Matrix.mul_assoc] using
      (compress_inverseCongruence V D hV).symm
  have hH : pairModel U (probedImageBasis (rfcMethod fullMemory 1)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)=Rᵀ*base*R := by
    rw [reference_model_gram base hb,fullBasisMatrix_compression]
  have hr : frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k=
      cgOperator (Rᵀ*metricRoot base) (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1)) := by
    rw [frozenIncoming_reference_fresh base hb g k hN,projectedResidual_fullBasisMatrix]
    simp only [R,U,map_mul,mul_apply_eq_comp,cgOperator]
  change cgOperator (metricRoot base)⁻¹ (cgOperator (Rᵀ⁻¹*(D*_⁻¹)) _)=_
  conv_lhs => rw [hD,hH,hr]
  simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_smul] using
    full_reference_coefficient base R S hb hR
      (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1))

/-- The actual full modified RFC solve has the source canonical factor 𝓛−Δ̂ with a genuine cubic remainder.
Use: informed model changes operate on the real RFC prefix and real terminal query, with all reference scales eliminated.
Article: main_krylov, apD:lem-model, A^(−1/2)g₊=−‖ŝ_last‖(𝓛−Δ̂)f̂+O(ω³).
Proof: primitive canonical operators discharge every actual prefix and
modified inverse domain in the full physical theorem. Normalize that true
cubic remainder by the fixed inverse metric root, then identify both the
original native factor and the subtracted actual model change exactly. -/
theorem full_modified_canonical_second_order {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hEsym : ∀ z i, (E z i).IsSymm)
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hD : AnalyticAt ℝ D 0) (hD0 : D 0=0) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g k)
    (fun z => cgOperator (metricRoot base)⁻¹ (modifiedTerminalGradient (A z) (B z) g k (D z))+
      ‖canonicalCGStep base g k‖ •
        ((staircaseOperator base g (E z) (F z k) (k+1)-cgOperator (inverseCongruence V (D z)))
          (freshDefect base g (E z) (k+1)))) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- All actual operator families, including independent intermediate corrections, are genuine analytic source data.
  let A := fun z => canonicalFCPath base (E z) 1
  let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
  have hA (i : ℕ) : AnalyticAt ℝ (fun z => A z i) 0 :=
    canonicalFCPath_analyticAt (fun _ => base) E 0 analyticAt_const
      (Eventually.of_forall fun _ => hb) hE i
  have hB (i : ℕ) : AnalyticAt ℝ (fun z => B z i) 0 := by
    have hm : AnalyticAt ℝ (fun z => metricRoot base*F z i*metricRoot base) 0 :=
      (analyticAt_const.mul (hF i)).mul analyticAt_const
    exact (hA i).add ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hA0 : A 0=(fun _ => cgOperator base) := canonicalFCPath_at_zero base (E 0) hE0
  have hB0 : B 0=(fun _ => cgOperator base) := by
    funext i
    simp only [B,canonicalCorrectionOperator,hF0,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,add_zero]
    exact congrFun hA0 i
  have hpos := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hn := full_modified_physical_second_order A B (fun _ => g) hA hB analyticAt_const
    (fun z i => canonicalFCPath_symmetric base hb (E z) (hEsym z) 1 i)
    (cgOperator base) hA0 hB0 hpos.1 hpos.2 hk hpre D hD hD0
  let U := referenceModelBasis base g k
  let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
    (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
  let R := fullBasisMatrix U
  let L := fun z => Matrix.of fun i j : Fin (k+1) => inner ℝ (U i)
    ((B z k-A z (k-(min i j).val)) (U j))
  have hn' : (fun z => modifiedTerminalGradient (A z) (B z) g k (D z)+
      cgOperator (Rᵀ⁻¹*((L z-D z)*H⁻¹))
        (frozenIncoming (cgOperator base) g (A z) k)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
    simpa only [hA0,hB0,U,H,R,L,referenceModelBasis,cgOperator] using hn
  have ho := operator_action_order (fun _ : X => cgOperator (metricRoot base)⁻¹) _
    (fun _ => 1) (fun z => ‖z‖^3) (continuousAt_const.tendsto.isBigO_one ℝ) hn'
  have ho' : (fun z => cgOperator (metricRoot base)⁻¹
      (modifiedTerminalGradient (A z) (B z) g k (D z)+
        cgOperator (Rᵀ⁻¹*((L z-D z)*H⁻¹))
          (frozenIncoming (cgOperator base) g (A z) k))) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
    simpa only [one_mul] using ho
  -- Split the genuine native coefficient before identifying each exact canonical term.
  apply ho'.congr_left
  intro z
  have hsplit : cgOperator (Rᵀ⁻¹*((L z-D z)*H⁻¹))
      (frozenIncoming (cgOperator base) g (A z) k)=
      cgOperator (Rᵀ⁻¹*(L z*H⁻¹)) (frozenIncoming (cgOperator base) g (A z) k)-
        cgOperator (Rᵀ⁻¹*(D z*H⁻¹)) (frozenIncoming (cgOperator base) g (A z) k) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,cgOperator,map_sub,_root_.sub_apply]
  have hL : cgOperator (metricRoot base)⁻¹
      (cgOperator (Rᵀ⁻¹*(L z*H⁻¹)) (frozenIncoming (cgOperator base) g (A z) k))=
      ‖canonicalCGStep base g k‖ • staircaseOperator base g (E z) (F z k) (k+1)
        (freshDefect base g (E z) (k+1)) := native_coefficient_canonical base hb g hN (E z) (F z k)
  have hΔ : cgOperator (metricRoot base)⁻¹
      (cgOperator (Rᵀ⁻¹*(D z*H⁻¹)) (frozenIncoming (cgOperator base) g (A z) k))=
      ‖canonicalCGStep base g k‖ • cgOperator (inverseCongruence (metricRoot base*R) (D z))
        (freshDefect base g (E z) (k+1)) := native_model_change_canonical base hb g hN (E z) (D z)
  rw [map_add,hsplit,map_sub,hL,hΔ]
  simp only [_root_.sub_apply,smul_sub]
  rfl

end
end krylov.Correction
