import polyak.FiniteHorizon.BlockCompact
import polyak.FiniteHorizon.Closure

/-!
Article: Appendix C, dimension-free compactness of normalized endpoint windows.
Use: all admissible endpoint pairs are continuous images of one fixed-dimensional
global Gram cone, and every point of that image is an actual finite-memory block.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Interpolation Matrix
open scoped BigOperators Topology Matrix.Norms.Elementwise

def sliceWindow {H p : ℕ} (l : ℕ) (hl : l≤p) (Y : WindowSpace (H+p)) : WindowSpace H :=
  ((fun i j => Y.1 ⟨l+i.val,by omega⟩ ⟨l+j.val,by omega⟩),
    fun i => Y.2 ⟨l+i.val,by omega⟩)

@[fun_prop] theorem continuous_sliceWindow {H p : ℕ} (l : ℕ) (hl : l≤p) :
    Continuous (sliceWindow (H:=H) l hl) := by unfold sliceWindow; fun_prop

theorem trace_sliceWindow_zero {H p : ℕ} (Y : WindowSpace (H+p)) :
    traceWindow (sliceWindow 0 (Nat.zero_le p) Y)=blockPrefixTrace H (H+p) (by omega) Y := by
  unfold traceWindow Matrix.trace sliceWindow blockPrefixTrace
  simp only [zero_add]
  rfl

theorem sliceWindow_segmentOfBlock {A B β : ℝ} {H p : ℕ} (hB : B≠0)
    {Y : WindowSpace (H+p)} (hY : Y∈blockCone A B β H (H+p))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin (H+p+2) → E) (hx : Matrix.gram ℝ x=Y.1) (l : ℕ) (hl : l≤p) :
    sliceWindow l hl Y=segmentWindow (segmentOfBlock hB hY x hx) (H+l) := by
  have hidx : H+l-H=l:=by omega
  apply Prod.ext
  · ext i j
    change Y.1 ⟨l+i.val,by omega⟩ ⟨l+j.val,by omega⟩=
      inner ℝ (realizedPosition x (H+l-H+i)) (realizedPosition x (H+l-H+j))
    rw [hidx,←hx]
    have hi:=realizedPosition_fin x (⟨l+i.val,by omega⟩ : Fin (H+p+2))
    have hj:=realizedPosition_fin x (⟨l+j.val,by omega⟩ : Fin (H+p+2))
    rw [hi,hj]
    rfl
  · ext i
    change Y.2 ⟨l+i.val,by omega⟩=realizedValue Y.2 (H+l-H+(i+1))
    rw [hidx,←Nat.add_assoc]
    exact (realizedValue_succ Y.2 (⟨l+i.val,by omega⟩ : Fin (H+p))).symm

/-- The full finite Gram-and-value table of an arbitrary H-segment. -/
def blockOfSegment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n) : WindowSpace n :=
  (Matrix.gram ℝ (fun i : Fin (n+2) => s.x i),fun i : Fin n => s.value (i+1))

theorem block_reconstructedGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H n : ℕ} (hB : B≠0) (s : HSegment E A B β H n) (i : Fin n) :
    reconstructedGradient (fun j : Fin (n+2) => s.x j) A B β i=s.σ (i+1) := by
  rw [reconstructedGradient,combination_gradient]
  change (1/B) • (s.x (i.val+2)-A • s.x (i.val+1)+β • s.x i.val)=_
  have hr:=s.recurrence i.val i.isLt
  rw [hr]
  have he : A • s.x (i.val+1)+B • s.σ (i.val+1)-β • s.x i.val-
      A • s.x (i.val+1)+β • s.x i.val=B • s.σ (i.val+1):=by module
  rw [he,smul_smul,one_div_mul_cancel hB,one_smul]

theorem blockOfSegment_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H n : ℕ} (hB : B≠0) (s : HSegment E A B β H n) :
    blockOfSegment s∈blockCone A B β H n := by
  refine ⟨Matrix.posSemidef_gram ℝ _,?_,?_⟩
  · intro i
    dsimp only [blockOfSegment]
    rw [starT_realization,starR_realization,block_reconstructedGradient hB s i]
    exact s.origin (i+1) (by omega) (by omega)
  · intro i j hij
    dsimp only [blockOfSegment]
    rw [pairT_realization,pairR_realization,block_reconstructedGradient hB s i,
      block_reconstructedGradient hB s j]
    exact s.interpolation (i+1) (by omega) (by omega) (j+1) (by omega) (by omega)
      (by simpa only [Nat.dist_add_add_right] using hij)

theorem sliceWindow_blockOfSegment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H p : ℕ} (s : HSegment E A B β H (H+p)) (l : ℕ) (hl : l≤p) :
    sliceWindow l hl (blockOfSegment s)=segmentWindow s (H+l) := by
  have hidx : H+l-H=l:=by omega
  apply Prod.ext
  · ext i j
    change inner ℝ (s.x (l+i)) (s.x (l+j))=inner ℝ (s.x (H+l-H+i)) (s.x (H+l-H+j))
    rw [hidx]
  · ext i
    change s.value (l+i+1)=s.value (H+l-H+(i+1))
    rw [hidx,Nat.add_assoc]

/-- The actual normalized endpoint-pair set, represented in one fixed finite dimension. -/
def normalizedEndpointPairs (A B β : ℝ) (H p : ℕ) : Set (WindowSpace H × WindowSpace H) :=
  (fun Y => (sliceWindow 0 (Nat.zero_le p) Y,sliceWindow p le_rfl Y)) ''
    {Y : WindowSpace (H+p) | Y∈blockCone A B β H (H+p) ∧
      blockPrefixTrace H (H+p) (by omega) Y=1}

theorem normalizedEndpointPairs_isCompact (A B β : ℝ) (H p : ℕ) (hB : B≠0) :
    IsCompact (normalizedEndpointPairs A B β H p) :=
  (normalized_block_isCompact A B β H (H+p) hB (by omega)).image
    ((continuous_sliceWindow 0 (Nat.zero_le p)).prodMk (continuous_sliceWindow p le_rfl))

/-- Every endpoint pair in the compact set is realized by a genuine H-segment. -/
theorem normalizedEndpointPairs_sound {A B β : ℝ} {H p : ℕ} (hB : B≠0)
    {Y : WindowSpace H × WindowSpace H} (hY : Y∈normalizedEndpointPairs A B β H p) :
    ∃ s : HSegment (EuclideanSpace ℝ (Fin (H+p+2))) A B β H (H+p),
      Y.1=segmentWindow s H ∧ Y.2=segmentWindow s (H+p) ∧ traceWindow Y.1=1 := by
  obtain ⟨W,hW,hY⟩:=hY
  obtain ⟨x,hx⟩:=exists_gram_vectors hW.1.1
  refine ⟨segmentOfBlock hB hW.1 x hx,?_,?_,?_⟩
  · rw [←hY]
    simpa only [Nat.add_zero] using sliceWindow_segmentOfBlock hB hW.1 x hx 0 (Nat.zero_le p)
  · rw [←hY]
    exact sliceWindow_segmentOfBlock hB hW.1 x hx p le_rfl
  · rw [←hY,trace_sliceWindow_zero]
    exact hW.2

/-- Every normalized actual finite block, in any real Hilbert dimension, lies in that compact set. -/
theorem normalizedEndpointPairs_complete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H p : ℕ} (hB : B≠0) (s : HSegment E A B β H (H+p))
    (ht : traceWindow (segmentWindow s H)=1) :
    (segmentWindow s H,segmentWindow s (H+p))∈normalizedEndpointPairs A B β H p := by
  refine ⟨blockOfSegment s,⟨blockOfSegment_mem hB s,?_⟩,?_⟩
  · rw [←trace_sliceWindow_zero,sliceWindow_blockOfSegment]
    simpa only [Nat.add_zero] using ht
  · apply Prod.ext
    · simpa only [Nat.add_zero] using sliceWindow_blockOfSegment s 0 (Nat.zero_le p)
    · exact sliceWindow_blockOfSegment s p le_rfl

end polyak.FiniteHorizon
