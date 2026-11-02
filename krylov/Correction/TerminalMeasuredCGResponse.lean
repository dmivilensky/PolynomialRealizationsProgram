import krylov.Correction.TerminalModelQuery
import krylov.Correction.TerminalFreshCoordinates
import krylov.Correction.TerminalCGResponse

/-!
Article: main_krylov, thm:UCq, quantitative terminal CG response assembly.
Use: Combine true observed model and search data with the original CG
staircase coefficient, retaining explicit uniform cubic constants.
Source: the proved actual measured-query cubic inequality, real incoming
fresh response, reference-weighted oblique comparison and exact CG dictionary.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in
/-- A genuine chronological measured correction has the original energy-scaled CG staircase/fresh-defect coefficient with an explicit cubic remainder from its real prefix and search bounds.
Use: Assemble the uniform ordinary-RFC response without an assumed expansion, artificial model-error factor or smallest reference energy.
Article: main_krylov, thm:UCq.
Proof: Derive the true incoming fresh-vector error from actual observed conjugacy and the old projected residual. The genuine measured-model cubic theorem controls its actual query around the moving staircase. Keep the true last reference line norm in every old-flag comparison, giving a cubic staircase-action change. Exact CG reference identities recover the original coefficient and terminal error norm. The finite source's last zero increment is removed exactly.
-/
theorem terminal_measured_cg_response {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hcount : referenceAtomCount base hb g=k+1)
    (t y : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (ht : ∀ i, ‖t i‖=1)
    (A E : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hInc : ∀ j<k+1, A (j+1)-A j=E j) (hE : E k=0)
    (G line : EuclideanSpace ℝ (Fin (k+1)))
    {a b c W V R L D H ε : ℝ}
    (ha : 0≤a) (hb' : 0≤b) (hc : 0≤c) (hW : 0≤W) (hV : 0≤V)
    (hR : 0≤R) (hL : 0≤L) (hD : 0≤D) (hH : 0≤H)
    (hε : 0≤ε) (hε1 : ε≤1) (haε : a*ε≤1/2) (hbε : b*ε≤1/2)
    (hGram : ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤a*ε)
    (hModel : ‖latest (crossGram t y)-1‖≤b*ε)
    (hy : ∀ i, ‖y i-cgOperator (A i.val) (t i)‖≤c*ε^2)
    (hbudget : (∑ l ∈ range (k+1), ‖E l‖)≤W*ε) (hF : ‖F‖≤V*ε)
    (hold : ‖projectedResidual (fun i : Fin k => t i.castSucc) G‖≤R*ε^2)
    (hconj : ∀ i : Fin k, inner ℝ (y i.castSucc) line=0)
    (hcurrent : inner ℝ (t (Fin.last k)) (G+cgOperator (A k) line)=0)
    (hline : ‖line‖≤L) (hstep : ‖line-canonicalCGStep base g k‖≤D*ε)
    (hflag : ∀ l<k, ‖cgCanonicalError base g k‖*
      ‖transportedFlag (fullBasisMatrix t) l-transportedFlag (canonicalCGUnitMatrix base g) l‖≤H*ε) :
    let e := 2*Real.sqrt (k+1)*(R+c*L)
    let d := 4*W+V
    let r := 2*W*L
    let Cq := (8*((k+1 : ℕ) : ℝ)*c+d*(8*b+4*a))*(r+e)+d*e
    let Cf := (4*W+V)*W*(2*((k+1 : ℕ) : ℝ)*D+H)+8*W^2*H
    let v := G+cgOperator (A k) line
    ‖v+cgOperator (A (k+1)+F) (combine t (modelCoefficients t (latest (crossGram t y)) v))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))‖≤
      (Cq+Cf)*ε^3 := by
  let T := fullBasisMatrix t
  let Q := canonicalCGUnitMatrix base g
  let f := obliqueResponse T E (terminalLineSequence (k+1) line)
  let fq := obliqueResponse Q E (terminalLineSequence (k+1) (canonicalCGStep base g k))
  let e := 2*Real.sqrt (k+1)*(R+c*L)
  let d := 4*W+V
  let r := 2*W*L
  let v := G+cgOperator (A k) line
  have he : 0≤e := by dsimp only [e]; positivity
  have hd : 0≤d := by dsimp only [d]; positivity
  have hGhalf := hGram.trans haε
  have hQhalf : ‖Qᵀ*Q-1‖≤(1/2 : ℝ) := by
    rw [show Qᵀ*Q=1 from canonicalCGUnitMatrix_gram base hb g hcount,sub_self,norm_zero]
    norm_num
  have hfincoming := terminal_incoming_fresh_bound t A E hA
    (fun j hj => hInc j (by omega)) G line (fun i => y i.castSucc)
    (mul_nonneg hc (sq_nonneg ε)) hGhalf hold (fun i => hy i.castSucc) hconj hcurrent
  have hvf : ‖v-f‖≤e*ε^2 := by
    apply hfincoming.trans
    calc
      _ ≤ 2*Real.sqrt (k+1)*(R*ε^2+(c*ε^2)*L) := by
        gcongr
      _ = _ := by dsimp only [e]; ring
  have hf : ‖f‖≤r*ε := by
    apply (terminal_oblique_response_norm T E line hGhalf).trans
    calc
      _ ≤ 2*(W*ε)*L := by gcongr
      _ = _ := by dsimp only [r]; ring
  have hstair : ‖obliqueStaircase T E F (k+1)‖≤d*ε := by
    apply (obliqueStaircase_norm T E F (k+1) hGhalf).trans
    exact (add_le_add (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ)≤4)) hF).trans_eq
      (by dsimp only [d]; ring)
  have hquery := terminal_measured_query_cubic t y ht A E F hA hInc v f
    ha hb' hc hd he hε hε1 haε hbε hGram hModel hy hstair hvf hf
  have hzeroT := obliqueStaircase_succ_of_zero T E F k hE
  rw [hzeroT] at hquery
  have hsame : (∑ l ∈ range k, ‖E l‖)=∑ l ∈ range (k+1), ‖E l‖ := by
    rw [sum_range_succ,hE,norm_zero,add_zero]
  have hbudold : (∑ l ∈ range k, ‖E l‖)≤W*ε := hsame.trans_le hbudget
  have hnorm : ‖cgCanonicalError base g k‖=‖canonicalCGStep base g k‖ :=
    terminal_step_error_norm base hb g hcount.ge
  have hflags l (hl : l<k+1-1) : ‖canonicalCGStep base g k‖*‖transportedFlag T l-transportedFlag Q l‖≤H*ε := by
    rw [← hnorm]
    exact hflag l (by omega)
  have hcompare := terminal_staircase_response_difference T Q E F line (canonicalCGStep base g k)
    (mul_nonneg hD hε) (mul_nonneg hH hε) hGhalf hQhalf hstep hflags
  dsimp only at hcompare
  simp only [Nat.add_sub_cancel] at hcompare
  have hcompare' : ‖cgOperator (obliqueStaircase T E F k) f-
      cgOperator (obliqueStaircase Q E F k) fq‖≤
      ((4*W+V)*W*(2*((k+1 : ℕ) : ℝ)*D+H)+8*W^2*H)*ε^3 := by
    apply hcompare.trans
    calc
      _ ≤ (4*(W*ε)+V*ε)*((W*ε)*(2*((k+1 : ℕ) : ℝ)*(D*ε)+H*ε))+
          8*(W*ε)*(W*ε)*(H*ε) := by
        gcongr
      _ = _ := by ring
  have href : cgOperator (obliqueStaircase Q E F k) fq=
      ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1)) := by
    dsimp only [fq,Q]
    have hsq := canonicalCG_obliqueStaircase base hb g hcount E F
    have hfq := canonicalCG_terminal_obliqueResponse base hb g hcount E
    simp only [Nat.add_sub_cancel] at hsq hfq
    rw [hsq,hfq,map_smul,← hnorm]
  rw [href] at hcompare'
  dsimp only
  have hsplit : v+cgOperator (A (k+1)+F) (combine t (modelCoefficients t (latest (crossGram t y)) v))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))=
      (v+cgOperator (A (k+1)+F) (combine t (modelCoefficients t (latest (crossGram t y)) v))+
        cgOperator (obliqueStaircase T E F k) f)-
      (cgOperator (obliqueStaircase T E F k) f-
        ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))) := by abel
  change ‖v+cgOperator (A (k+1)+F) (combine t (modelCoefficients t (latest (crossGram t y)) v))+
    ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))‖≤_
  rw [hsplit]
  exact (norm_sub_le _ _).trans ((add_le_add hquery hcompare').trans_eq (by dsimp only [d,r,e]; ring))

end
end krylov.Correction
