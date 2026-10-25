import polyak.Growth.GramWindow
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
Article: Appendix C, semantic realization and bounded normalized Gram windows.
Use: the closed finite-dimensional cone is precisely a cone of actual interpolation data.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section
open Interpolation Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def combination {H : ℕ} (x : Fin (H+2) → E) (a : Fin (H+2) → ℝ) : E := ∑ i,a i • x i

theorem combination_add {H : ℕ} (x : Fin (H+2) → E) (a b : Fin (H+2) → ℝ) :
    combination x (a+b)=combination x a+combination x b := by
  simp [combination,add_smul,Finset.sum_add_distrib]

theorem combination_sub {H : ℕ} (x : Fin (H+2) → E) (a b : Fin (H+2) → ℝ) :
    combination x (a-b)=combination x a-combination x b := by
  simp [combination,sub_smul,Finset.sum_sub_distrib]

theorem combination_smul {H : ℕ} (x : Fin (H+2) → E) (c : ℝ) (a : Fin (H+2) → ℝ) :
    combination x (c • a)=c • combination x a := by
  simp [combination,smul_smul,Finset.smul_sum]

theorem combination_single {H : ℕ} (x : Fin (H+2) → E) (i : Fin (H+2)) :
    combination x (Pi.single i 1)=x i := by
  classical
  simp [combination,Pi.single_apply,ite_smul]

theorem combination_position {H : ℕ} (x : Fin (H+2) → E) (i : Fin H) :
    combination x (positionCoefficient i)=x i.castSucc.succ := combination_single x _

theorem combination_gradient {H : ℕ} (x : Fin (H+2) → E) (A B β : ℝ) (i : Fin H) :
    combination x (gradientCoefficient A B β i)=
      (1/B) • (x i.succ.succ-A • x i.castSucc.succ+β • x i.castSucc.castSucc) := by
  simp only [gradientCoefficient,combination_smul,combination_add,combination_sub,
    combination_single,combination_position]

/-- Article: the linear Gram pairing is the genuine inner product of the reconstructed vectors. -/
theorem gramPair_realization {H : ℕ} (x : Fin (H+2) → E) (v : Fin H → ℝ)
    (a b : Fin (H+2) → ℝ) :
    gramPair a b (Matrix.gram ℝ x,v)=inner ℝ (combination x a) (combination x b) := by
  rw [gramPair_apply]
  unfold combination
  rw [sum_inner]
  simp only [Matrix.gram_apply,inner_sum,real_inner_smul_left,inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def reconstructedGradient {H : ℕ} (x : Fin (H+2) → E) (A B β : ℝ) (i : Fin H) : E :=
  combination x (gradientCoefficient A B β i)

theorem starT_realization {H : ℕ} (x : Fin (H+2) → E) (v : Fin H → ℝ)
    (A B β : ℝ) (i : Fin H) :
    starT A B β i (Matrix.gram ℝ x,v)=v i-(1/2 : ℝ)*
      inner ℝ (reconstructedGradient x A B β i) (x i.castSucc.succ) := by
  simp only [starT,_root_.sub_apply,_root_.smul_apply,
    valueCoordinate,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,gramPair_realization,combination_position,
    reconstructedGradient]
  rfl

theorem starR_realization {H : ℕ} (x : Fin (H+2) → E) (v : Fin H → ℝ)
    (A B β : ℝ) (i : Fin H) :
    starR A B β i (Matrix.gram ℝ x,v)=(1/4 : ℝ)*
      (‖x i.castSucc.succ‖^2-‖reconstructedGradient x A B β i‖^2) := by
  simp only [starR,_root_.sub_apply,_root_.smul_apply,
    smul_eq_mul,gramPair_realization,combination_position,reconstructedGradient,
    real_inner_self_eq_norm_sq]

theorem pairT_realization {H : ℕ} (x : Fin (H+2) → E) (v : Fin H → ℝ)
    (A B β : ℝ) (i j : Fin H) :
    pairT A B β i j (Matrix.gram ℝ x,v)=v j-v i-(1/2 : ℝ)*
      inner ℝ (reconstructedGradient x A B β i+reconstructedGradient x A B β j)
        (x j.castSucc.succ-x i.castSucc.succ) := by
  simp only [pairT,_root_.sub_apply,_root_.smul_apply,
    valueCoordinate,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,gramPair_realization,combination_add,
    combination_sub,combination_position,reconstructedGradient]
  rfl

theorem pairR_realization {H : ℕ} (x : Fin (H+2) → E) (v : Fin H → ℝ)
    (A B β : ℝ) (i j : Fin H) :
    pairR A B β i j (Matrix.gram ℝ x,v)=(1/4 : ℝ)*
      (‖x j.castSucc.succ-x i.castSucc.succ‖^2-
        ‖reconstructedGradient x A B β j-reconstructedGradient x A B β i‖^2) := by
  simp only [pairR,_root_.sub_apply,_root_.smul_apply,
    smul_eq_mul,gramPair_realization,combination_sub,combination_position,reconstructedGradient,
    real_inner_self_eq_norm_sq]

def realizedPosition {H : ℕ} (x : Fin (H+2) → E) (k : ℕ) : E := x (Segment.finiteIndex H k)

def realizedGradient {H : ℕ} (x : Fin (H+2) → E) (A B β : ℝ) (k : ℕ) : E :=
  if hk : 1 ≤ k ∧ k ≤ H then reconstructedGradient x A B β ⟨k-1,by omega⟩ else 0

def realizedValue {H : ℕ} (v : Fin H → ℝ) (k : ℕ) : ℝ :=
  if hk : 1 ≤ k ∧ k ≤ H then v ⟨k-1,by omega⟩ else 0

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem realizedPosition_fin {H : ℕ} (x : Fin (H+2) → E) (i : Fin (H+2)) :
    realizedPosition x i=x i := by
  unfold realizedPosition
  congr 1
  apply Fin.ext
  simp only [Segment.finiteIndex]
  exact min_eq_left (by omega)

theorem realizedGradient_succ {H : ℕ} (x : Fin (H+2) → E) (A B β : ℝ) (i : Fin H) :
    realizedGradient x A B β (i+1)=reconstructedGradient x A B β i := by
  unfold realizedGradient
  rw [dite_eq_left (show 1 ≤ (i : ℕ)+1 ∧ (i : ℕ)+1 ≤ H by omega)]
  congr 1

theorem realizedValue_succ {H : ℕ} (v : Fin H → ℝ) (i : Fin H) :
    realizedValue v (i+1)=v i := by
  unfold realizedValue
  rw [dite_eq_left (show 1 ≤ (i : ℕ)+1 ∧ (i : ℕ)+1 ≤ H by omega)]
  congr 1

/-- Article: every finite Gram-cone element reconstructs the literal interior interpolation table. -/
def rawOfWindow {A B β : ℝ} {H : ℕ} (hB : B≠0) {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) (x : Fin (H+2) → E) (hgram : Matrix.gram ℝ x=Y.1) :
    RawSegment E A B β H where
  x := realizedPosition x
  σ := realizedGradient x A B β
  value := realizedValue Y.2
  interpolation i hi hin j hj hjn := by
    let I : Fin H := ⟨i-1,by omega⟩
    let J : Fin H := ⟨j-1,by omega⟩
    have hI : (I : ℕ)+1=i := by dsimp only [I]; omega
    have hJ : (J : ℕ)+1=j := by dsimp only [J]; omega
    have hposI : realizedPosition x i=x I.castSucc.succ := by
      rw [← hI]
      exact realizedPosition_fin x I.castSucc.succ
    have hposJ : realizedPosition x j=x J.castSucc.succ := by
      rw [← hJ]
      exact realizedPosition_fin x J.castSucc.succ
    have hgradI : realizedGradient x A B β i=reconstructedGradient x A B β I := by
      rw [← hI,realizedGradient_succ]
    have hgradJ : realizedGradient x A B β j=reconstructedGradient x A B β J := by
      rw [← hJ,realizedGradient_succ]
    have hvalI : realizedValue Y.2 i=Y.2 I := by rw [← hI,realizedValue_succ]
    have hvalJ : realizedValue Y.2 j=Y.2 J := by rw [← hJ,realizedValue_succ]
    have hYP : Y=(Matrix.gram ℝ x,Y.2) := Prod.ext hgram.symm rfl
    have hh := hY.2.2 I J
    rw [hYP,pairT_realization,pairR_realization] at hh
    simpa only [datumT,datumR,hposI,hposJ,hgradI,hgradJ,hvalI,hvalJ] using hh
  origin i hi hin := by
    let I : Fin H := ⟨i-1,by omega⟩
    have hI : (I : ℕ)+1=i := by dsimp only [I]; omega
    have hposI : realizedPosition x i=x I.castSucc.succ := by
      rw [← hI]
      exact realizedPosition_fin x I.castSucc.succ
    have hgradI : realizedGradient x A B β i=reconstructedGradient x A B β I := by
      rw [← hI,realizedGradient_succ]
    have hvalI : realizedValue Y.2 i=Y.2 I := by rw [← hI,realizedValue_succ]
    have hYP : Y=(Matrix.gram ℝ x,Y.2) := Prod.ext hgram.symm rfl
    have hh := hY.2.1 I
    rw [hYP,starT_realization,starR_realization] at hh
    simpa only [hposI,hgradI,hvalI] using hh
  recurrence k hk := by
    let I : Fin H := ⟨k,hk⟩
    have hgrad : realizedGradient x A B β (k+1)=
        (1/B) • (x I.succ.succ-A • x I.castSucc.succ+β • x I.castSucc.castSucc) := by
      rw [show k+1=(I : ℕ)+1 from rfl,realizedGradient_succ]
      exact combination_gradient x A B β I
    have hleft : realizedPosition x k=x I.castSucc.castSucc := realizedPosition_fin x I.castSucc.castSucc
    have hmid : realizedPosition x (k+1)=x I.castSucc.succ := realizedPosition_fin x I.castSucc.succ
    have hright : realizedPosition x (k+2)=x I.succ.succ := realizedPosition_fin x I.succ.succ
    rw [hgrad,hleft,hmid,hright,smul_smul,mul_one_div_cancel hB,one_smul]
    module

variable [CompleteSpace E]

/-- Article: continuation, every cone element is the exact window of one genuine infinite trajectory.
Both its complete Gram matrix and all H relative function values are preserved. -/
theorem windowCone_exists_run {A B β : ℝ} {H : ℕ} (hB : B≠0) {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) :
    ∃ r : Run (EuclideanSpace ℝ (Fin (H+2))) A B β,
      Matrix.gram ℝ (fun i : Fin (H+2) => r.x i)=Y.1 ∧
      ∀ i : Fin H,r.ψ (r.x (i+1))=Y.2 i := by
  obtain ⟨x,hx⟩ := exists_gram_vectors hY.1
  let s := rawOfWindow hB hY x hx
  obtain ⟨q,hq,hdata⟩ := s.exists_completion
  let w := HSegment.ofSegment q H
  obtain ⟨r,hpos,hψdata⟩ := w.exists_run_of_length_le (by omega)
  have hpositions (i : Fin (H+2)) : r.x i=x i := by
    rw [hpos i (by omega)]
    change q.x i=x i
    rw [hq]
    exact realizedPosition_fin x i
  refine ⟨r,?_,fun i => ?_⟩
  · rw [show (fun i : Fin (H+2) => r.x i)=x from funext hpositions]
    exact hx
  · have hh := (hψdata (i+1) (by omega) (by omega)).1
    change r.ψ (r.x (i+1))=q.value (i+1) at hh
    rw [hh,(hdata (i+1) (by omega) (by omega)).2]
    exact realizedValue_succ Y.2 i

/-- Article: the trace used for normalization is the trace of the Gram component only. -/
def traceWindow {H : ℕ} (Y : WindowSpace H) : ℝ := Matrix.trace Y.1

theorem traceWindow_continuous (H : ℕ) : Continuous (traceWindow : WindowSpace H → ℝ) := by
  unfold traceWindow Matrix.trace
  fun_prop

theorem traceWindow_nonneg {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) : 0 ≤ traceWindow Y := by
  unfold traceWindow Matrix.trace
  exact Finset.sum_nonneg (fun i _ => hY.1.diag_nonneg (i:=i))

theorem diag_le_traceWindow {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) (i : Fin (H+2)) : Y.1 i i ≤ traceWindow Y :=
  Finset.single_le_sum (fun j _ => hY.1.diag_nonneg (i:=j)) (Finset.mem_univ i)

/-- Article: PSD entries are controlled by half the sum of the two diagonal entries. -/
theorem matrix_entry_le_half_diag {H : ℕ} {G : WindowMatrix H} (hG : G.PosSemidef)
    (i j : Fin (H+2)) : |G i j| ≤ (G i i+G j j)/2 := by
  obtain ⟨x,hx⟩ := exists_gram_vectors hG
  have hinner := abs_real_inner_le_norm (x i) (x j)
  have he (a b : Fin (H+2)) : G a b=inner ℝ (x a) (x b) := by rw [← hx]; rfl
  rw [he i j,he i i,he j j,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg (‖x i‖-‖x j‖)]

theorem matrix_entry_le_traceWindow {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) (i j : Fin (H+2)) : |Y.1 i j| ≤ traceWindow Y := by
  have hh := matrix_entry_le_half_diag hY.1 i j
  linarith [diag_le_traceWindow hY i,diag_le_traceWindow hY j]

/-- Article: all supplied function values obey the sharp half-diagonal estimate. -/
theorem window_value_le_half_diag {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) (i : Fin H) :
    |Y.2 i| ≤ Y.1 i.castSucc.succ i.castSucc.succ/2 := by
  obtain ⟨x,hx⟩ := exists_gram_vectors hY.1
  have hYP : Y=(Matrix.gram ℝ x,Y.2) := Prod.ext hx.symm rfl
  have hh := hY.2.1 i
  rw [hYP,starT_realization,starR_realization] at hh
  let e := x i.castSucc.succ
  let g := reconstructedGradient x A B β i
  have hinner := abs_real_inner_le_norm g e
  have habs : |Y.2 i| ≤ |Y.2 i-(1/2 : ℝ)*inner ℝ g e|+(1/2 : ℝ)*|inner ℝ g e| := by
    have hh := abs_add_le (Y.2 i-(1/2 : ℝ)*inner ℝ g e) ((1/2 : ℝ)*inner ℝ g e)
    simpa only [sub_add_cancel,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] using hh
  have hdiag : Y.1 i.castSucc.succ i.castSucc.succ=‖e‖^2 := by
    rw [← hx]
    change inner ℝ e e=‖e‖^2
    exact real_inner_self_eq_norm_sq e
  rw [hdiag]
  change |Y.2 i-(1/2 : ℝ)*inner ℝ g e| ≤ (1/4 : ℝ)*(‖e‖^2-‖g‖^2) at hh
  nlinarith [sq_nonneg (‖e‖-‖g‖)]

/-- Article: the ambient finite-dimensional norm is controlled by the Gram trace. -/
theorem window_norm_le_trace {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) : ‖Y‖ ≤ traceWindow Y := by
  have htrace := traceWindow_nonneg hY
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg htrace).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg htrace).mpr
    intro j
    simpa only [Real.norm_eq_abs] using matrix_entry_le_traceWindow hY i j
  · apply (pi_norm_le_iff_of_nonneg htrace).mpr
    intro i
    have hv := window_value_le_half_diag hY i
    have hd := diag_le_traceWindow hY i.castSucc.succ
    rw [Real.norm_eq_abs]
    linarith

def matrixCoordinate {H : ℕ} (i j : Fin (H+2)) : WindowSpace H := (Matrix.single i j 1,0)

def valueBasis {H : ℕ} (i : Fin H) : WindowSpace H := (0,Pi.single i 1)

/-- Article: the sum of the absolute values of a price's actual coefficients. -/
def priceSize {H : ℕ} (L : WindowSpace H →L[ℝ] ℝ) : ℝ :=
  (∑ i,∑ j,|L (matrixCoordinate i j)|)+∑ i,|L (valueBasis i)|

theorem window_coordinate_expansion {H : ℕ} (Y : WindowSpace H) :
    Y=(∑ i,∑ j,Y.1 i j • matrixCoordinate i j)+∑ i,Y.2 i • valueBasis i := by
  classical
  apply Prod.ext
  · ext i j
    simp [matrixCoordinate,valueBasis,Prod.fst_sum,Matrix.sum_apply,Matrix.single_apply]
    simp_rw [ite_and]
    simp
  · ext i
    simp [matrixCoordinate,valueBasis,Prod.snd_sum,Pi.single_apply]

/-- Article: every linear price is bounded by its actual coefficient sum times the Gram trace. -/
theorem price_le_trace {A B β : ℝ} {H : ℕ} {Y : WindowSpace H}
    (hY : Y∈windowCone A B β H) (L : WindowSpace H →L[ℝ] ℝ) :
    |L Y| ≤ priceSize L*traceWindow Y := by
  have hdecomp : L Y=(∑ i,∑ j,Y.1 i j*L (matrixCoordinate i j))+
      ∑ i,Y.2 i*L (valueBasis i) := by
    conv_lhs => rw [window_coordinate_expansion Y]
    simp only [map_add,map_sum,map_smul,smul_eq_mul]
  have hvalues (i : Fin H) : |Y.2 i| ≤ traceWindow Y := by
    have hv := window_value_le_half_diag hY i
    have hd := diag_le_traceWindow hY i.castSucc.succ
    linarith [traceWindow_nonneg hY]
  calc
    |L Y| ≤ (∑ i,∑ j,|Y.1 i j| *|L (matrixCoordinate i j)|)+
        ∑ i,|Y.2 i| *|L (valueBasis i)| := by
      rw [hdecomp]
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_mul] using (Finset.abs_sum_le_sum_abs
          (fun j => Y.1 i j*L (matrixCoordinate i j)) Finset.univ)
      · simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun i => Y.2 i*L (valueBasis i)) Finset.univ
    _ ≤ (∑ i,∑ j,traceWindow Y*|L (matrixCoordinate i j)|)+
        ∑ i,traceWindow Y*|L (valueBasis i)| := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (matrix_entry_le_traceWindow hY i j) (abs_nonneg _)))
      · exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hvalues i) (abs_nonneg _))
    _=priceSize L*traceWindow Y := by
      simp_rw [← Finset.mul_sum]
      unfold priceSize
      ring

/-- Article: bounded trace slices of the actual closed Gram cone are compact. -/
theorem windowCone_trace_le_isCompact (A B β R : ℝ) (H : ℕ) :
    IsCompact {Y : WindowSpace H | Y∈windowCone A B β H ∧ traceWindow Y ≤ R} := by
  have hclosed : IsClosed {Y : WindowSpace H | Y∈windowCone A B β H ∧ traceWindow Y ≤ R} :=
    (windowCone_isClosed A B β H).inter
    (isClosed_le (traceWindow_continuous H) continuous_const)
  apply (isCompact_closedBall (0 : WindowSpace H) R).of_isClosed_subset hclosed
  intro Y hY
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (window_norm_le_trace hY.1).trans hY.2

/-- Article: the normalized section trY=1 used in the compact near-kernel argument is compact. -/
theorem windowCone_trace_one_isCompact (A B β : ℝ) (H : ℕ) :
    IsCompact {Y : WindowSpace H | Y∈windowCone A B β H ∧ traceWindow Y=1} := by
  apply (windowCone_trace_le_isCompact A B β 1 H).of_isClosed_subset
    ((windowCone_isClosed A B β H).inter (isClosed_eq (traceWindow_continuous H) continuous_const))
  intro Y hY
  exact ⟨hY.1,hY.2.le⟩

/-- Article: the concrete Gram-and-value window of an H-segment, centered at k. -/
def segmentWindow {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n) (k : ℕ) : WindowSpace H :=
  (Matrix.gram ℝ (fun i : Fin (H+2) => s.x (k-H+i)),fun i : Fin H => s.value (k-H+(i+1)))

omit [CompleteSpace E] in
theorem reconstructedGradient_window {A B β : ℝ} {H n : ℕ} (hB : B≠0)
    (s : HSegment E A B β H n) (k : ℕ) (hk : H ≤ k) (hkn : k ≤ n) (i : Fin H) :
    reconstructedGradient (fun j : Fin (H+2) => s.x (k-H+j)) A B β i=
      s.σ (k-H+(i+1)) := by
  rw [reconstructedGradient,combination_gradient]
  change (1/B) • (s.x (k-H+((i : ℕ)+2))-A • s.x (k-H+((i : ℕ)+1))+
    β • s.x (k-H+i))=s.σ (k-H+((i : ℕ)+1))
  have hrec := s.recurrence (k-H+i) (by omega)
  have hrec' : s.x (k-H+((i : ℕ)+2))=A • s.x (k-H+((i : ℕ)+1))+
      B • s.σ (k-H+((i : ℕ)+1))-β • s.x (k-H+i) := by
    simpa only [Nat.add_assoc] using hrec
  have he : s.x (k-H+((i : ℕ)+2))-A • s.x (k-H+((i : ℕ)+1))+
      β • s.x (k-H+i)=B • s.σ (k-H+((i : ℕ)+1)) := by rw [hrec']; module
  rw [he,smul_smul,one_div_mul_cancel hB,one_smul]

omit [CompleteSpace E] in
/-- Article: every actual admissible H-segment window lies in the proved closed convex cone. -/
theorem segmentWindow_mem {A B β : ℝ} {H n : ℕ} (hB : B≠0)
    (s : HSegment E A B β H n) (k : ℕ) (hk : H ≤ k) (hkn : k ≤ n) :
    segmentWindow s k∈windowCone A B β H := by
  refine ⟨Matrix.posSemidef_gram ℝ _,?_,?_⟩
  · intro i
    dsimp only [segmentWindow]
    rw [starT_realization,starR_realization,reconstructedGradient_window hB s k hk hkn i]
    exact s.origin (k-H+(i+1)) (by omega) (by omega)
  · intro i j
    dsimp only [segmentWindow]
    rw [pairT_realization,pairR_realization,reconstructedGradient_window hB s k hk hkn i,
      reconstructedGradient_window hB s k hk hkn j]
    exact s.interpolation (k-H+(i+1)) (by omega) (by omega) (k-H+(j+1)) (by omega) (by omega)
      (by unfold Nat.dist; omega)

omit [CompleteSpace E] in
/-- Article: the finite-dimensional Gram trace is exactly the previously bounded window energy. -/
theorem trace_segmentWindow {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n)
    (k : ℕ) (hk : H ≤ k) : traceWindow (segmentWindow s k)=windowTrace s.x H k := by
  classical
  unfold traceWindow segmentWindow Matrix.trace windowTrace
  simp only [Matrix.diag_apply,Matrix.gram_apply,real_inner_self_eq_norm_sq]
  apply Finset.sum_bij (fun (i : Fin (H+2)) _ => k-H+(i : ℕ))
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨j-(k-H),by omega⟩,Finset.mem_univ _,?_⟩
    change k-H+(j-(k-H))=j
    omega
  · intro i _
    rfl

end
end polyak.Growth.FiniteHorizon
