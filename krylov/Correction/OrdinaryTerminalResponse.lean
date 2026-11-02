import krylov.Correction.TerminalMeasuredCGResponse
import krylov.Correction.ScenarioModelCoordinates
import krylov.Correction.OrdinarySearchCoordinates
import krylov.Correction.ChronologicalModelBasis
import krylov.Correction.ChronologicalCorrection

/-!
Article: main_krylov, thm:UCq, actual original-source terminal response.
Use: Apply the quantitative terminal CG response to the real ordinary-RFC
query on the article's genuine finite symmetric increment/defect variables.
Source: the proved true source matrix dictionary, original measured gate and
query execution, exact canonical search equations and terminal response bounds.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in
/-- The actual original-source ordinary-RFC output has its genuine energy-scaled CG staircase coefficient and explicit cubic allowance whenever its real prefix and observed terminal bounds hold.
Use: Connect uniform actual-prefix estimates to the original finite-source terminal vector, preserving a zero last searched displacement.
Article: main_krylov, thm:UCq.
Proof: The actual source matrices have their true symmetric consecutive increments, last zero extension and original correction defect. Actual recorded secants and the real conjugacy inverse give normalized old search orthogonality, while genuine defined search gives its exact current zero coordinate. The actual searched-gradient and accepted-query dictionaries identify the real output with its true chronological measured solve. Apply the proved quantitative CG response to those same actual data; no terminal expansion or fictitious model-error factor is assumed.
-/
theorem ordinary_terminal_source_response {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1)))
    (hk : 0<k) (hcount : referenceAtomCount base hb g=k+1)
    {a b c W V Cr L D H ε : ℝ}
    (ha : 0≤a) (hb' : 0≤b) (hc : 0≤c) (hW : 0≤W) (hV : 0≤V)
    (hCr : 0≤Cr) (hL : 0≤L) (hD : 0≤D) (hH : 0≤H)
    (hε : 0≤ε) (hε1 : ε≤1) (haε : a*ε≤1/2) (hbε : b*ε≤1/2) :
    let A := scenarioProbe base Θ.val
    let B := scenarioCorrection base Θ.val
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
    let P := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
    let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
    let t := unitWindow S
    let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
    let T := fullBasisMatrix t
    let G := J (probedGradient m A B g k)
    let line := P (fullLineStep 1 A B g k)
    let E := matrixSequenceExtension k Θ.val.1
    let F := matrixSequenceExtension (k+1) Θ.val.2 k
    (∀ i, ‖t i‖=1) → ‖Tᵀ*T-1‖≤a*ε → ‖latest (crossGram t z)-1‖≤b*ε →
    (∀ i, ‖z i-canonicalOperator base (A i.val) (t i)‖≤c*ε^2) →
    (∑ l ∈ range (k+1), ‖E l‖)≤W*ε → ‖F‖≤V*ε →
    ‖projectedResidual (unitWindow (fun i : Fin k => P (probedStep m A B g i.val))) G‖≤Cr*ε^2 →
    IsUnit (crossGram (windowImages (selectedWindow fullMemory (methodRun m A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun m A B g k)))).det →
    ‖windowDefect (selectedWindow fullMemory (methodRun m A B g k))‖<1 →
    inner ℝ (probedDirection m A B g k) (A k (probedDirection m A B g k))≠0 →
    ‖line‖≤L → ‖line-canonicalCGStep base g k‖≤D*ε →
    (∀ l<k, ‖cgCanonicalError base g k‖*‖transportedFlag T l-
      transportedFlag (canonicalCGUnitMatrix base g) l‖≤H*ε) →
    let e := 2*Real.sqrt (k+1)*(Cr+c*L)
    let d := 4*W+V
    let r := 2*W*L
    let Cq := (8*((k+1 : ℕ) : ℝ)*c+d*(8*b+4*a))*(r+e)+d*e
    let Cf := (4*W+V)*W*(2*((k+1 : ℕ) : ℝ)*D+H)+8*W^2*H
    ‖J (probedGradient m A B g (k+1))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))‖≤
      (Cq+Cf)*ε^3 := by
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let P := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
  let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
  let t := unitWindow S
  let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
  let G := J (probedGradient m A B g k)
  let line := P (fullLineStep 1 A B g k)
  let E := matrixSequenceExtension k Θ.val.1
  let F := matrixSequenceExtension (k+1) Θ.val.2 k
  let Ah := scenarioCanonicalMatrix Θ.val
  dsimp only
  intro ht hGram hModel hxi hbudget hF hold hC hgate hcurv hline hstep hflag
  have hAi j : canonicalOperator base (A j)=cgOperator (Ah j) := scenarioProbe_canonicalMatrix base hb Θ.val j
  have hterminal := scenarioCanonicalMatrix_terminal Θ.val
  simp only [Nat.add_sub_cancel] at hterminal
  have hB : canonicalOperator base (B k)=cgOperator (Ah (k+1)+F) := by
    change canonicalOperator base (scenarioCorrection base Θ.val k)=cgOperator (scenarioCanonicalMatrix Θ.val (k+1)+F)
    rw [hterminal]
    exact scenarioCorrection_canonicalMatrix base hb Θ.val k
  have hpost : J (fullPostSearch 1 A B g k)=G+cgOperator (Ah k) line := by
    have hp : J (fullPostSearch 1 A B g k)=G+canonicalOperator base (A k) line :=
      ordinary_canonical_post_search base hb A B g k
    rw [hAi] at hp
    exact hp
  have hcoord := normalized_chronological_steps base m A B g k
  have himages := normalized_chronological_images base m A B g k
  change t=Fin.snoc (unitWindow (fun i : Fin k => P (probedStep m A B g i.val)))
    (NormedSpace.normalize (P (probedDirection m A B g k))) at hcoord
  change z=Fin.snoc
    (fun i : Fin k => ‖P (probedStep m A B g i.val)‖⁻¹ • J (probedSecant m A B g i.val))
    (‖P (probedDirection m A B g k)‖⁻¹ • J (probedProbe m A B g k)) at himages
  have hold' : ‖projectedResidual (fun i : Fin k => t i.castSucc) G‖≤Cr*ε^2 := by
    rw [hcoord]
    simpa only [Fin.snoc_castSucc] using hold
  have hlineDir : line=lineLength (probedGradient m A B g k) (probedDirection m A B g k)
      (A k (probedDirection m A B g k)) • P (probedDirection m A B g k) := by
    dsimp only [line,fullLineStep]
    rw [map_smul]
    rfl
  have hconj (i : Fin k) : inner ℝ (z i.castSucc) line=0 := by
    rw [himages,Fin.snoc_castSucc,real_inner_smul_left,hlineDir,real_inner_smul_right]
    have ho := ordinary_chronological_image_conjugacy base hb A B g k hC i
    change inner ℝ (J (probedSecant m A B g i.val)) (P (probedDirection m A B g k))=0 at ho
    rw [ho,mul_zero,mul_zero]
  have hcurrent : inner ℝ (t (Fin.last k)) (G+cgOperator (Ah k) line)=0 := by
    rw [hcoord,Fin.snoc_last,← hpost]
    exact ordinary_canonical_search_orthogonal base hb A B g k hcurv
  have hS0 i : S i≠0 := by
    intro hz
    have hi := ht i
    change ‖‖S i‖⁻¹ • S i‖=1 at hi
    simp only [hz,norm_zero,_root_.inv_zero,zero_smul] at hi
    norm_num at hi
  have hgateArray : ‖pairDefect (fun i : Fin k => probedStep m A B g (k-1-i.val))
      (fun i : Fin k => probedSecant m A B g (k-1-i.val))‖<1 := by
    rw [← full_probed_defect_norm m A B g k]
    exact hgate
  have hquery := ordinary_canonical_chronological_gradient base hb A B g k hk hgateArray hS0
  dsimp only at hquery
  change J (probedGradient m A B g (k+1))=J (fullPostSearch 1 A B g k)+
    canonicalOperator base (B k) (combine t (modelCoefficients t (latest (crossGram t z)) (J (fullPostSearch 1 A B g k)))) at hquery
  rw [hpost,hB] at hquery
  have hzero : E k=0 := scenario_last_increment_zero Θ.val
  have hbound := terminal_measured_cg_response base hb g hcount t z ht Ah E F
    (fun j => scenarioCanonicalMatrix_symm Θ j)
    (fun j _hj => scenarioCanonicalMatrix_increment Θ.val j) hzero G line
    ha hb' hc hW hV hCr hL hD hH hε hε1 haε hbε hGram hModel
    (fun i => by rw [← hAi]; exact hxi i) hbudget hF hold' hconj hcurrent hline hstep hflag
  dsimp only at hbound
  rw [← hquery] at hbound
  exact hbound

end
end krylov.Correction
