import krylov.Methods.HomogeneousProtocol
import krylov.Methods.VirtualCoordinates
import krylov.Methods.HistoryWindowCharts
import krylov.Methods.DeferredDirection

/-!
Article: main_krylov, thm:D and lem:U, actual observed-history homogeneity.
Use: common scaling preserves the genuine newest-first stored secants and
all concrete retained-window solves, also on singular totalized data.
Source: true gradient differences, finite getter coordinates and the
already proved bilinear Gram/inverse coefficient covariance.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale both physical vectors of each genuinely observed stored pair. -/
def orderScalePairs (c : ℝ) (W : List (E × E)) : List (E × E) :=
  W.map (fun p=>(c • p.1,c • p.2))

/-- Actual observed secants scale with their true recorded vectors. -/
theorem orderScaleHistory_pairs (c : ℝ) (H : History E) :
    (scaleHistory c H).pairs=orderScalePairs c H.pairs := by
  rcases H with ⟨g,rs⟩
  change recordPairs (c • g) (rs.map (scaleRecord c))=orderScalePairs c (recordPairs g rs)
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    change (c • r.step,c • r.gradient-(scaleHistory c (⟨g,rs⟩ : History E)).gradient)::
      recordPairs (c • g) (rs.map (scaleRecord c))=_
    rw [scaleHistory_gradient,←smul_sub,ih]
    rfl

/-- Scaling preserves the actual retained suffix and its real length. -/
theorem orderScaleHistory_selected (memory : ℕ → ℕ) (c : ℝ) (H : History E) :
    selectedWindow memory (scaleHistory c H)=orderScalePairs c (selectedWindow memory H) := by
  rw [selectedWindow,orderScaleHistory_pairs]
  simp only [scaleHistory,List.length_map,orderScalePairs,selectedWindow,←List.map_take]

/-- Missing zero-default observations also commute with common scaling. -/
theorem orderScalePairs_getD (c : ℝ) (W : List (E × E)) (i : ℕ) :
    (orderScalePairs c W).getD i (0,0)=(c • (W.getD i (0,0)).1,c • (W.getD i (0,0)).2) := by
  simp only [orderScalePairs,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases W[i]? <;> simp

/-- The genuine retained conjugacy direction scales on every supplied
window, including all totalized singular solves. -/
theorem orderScalePairs_direction (c : ℝ) (hc : c≠0) (W : List (E × E)) (g : E) :
    windowDirection (orderScalePairs c W) (c • g)=c • windowDirection W g := by
  have hlen : (orderScalePairs c W).length=W.length := List.length_map _
  rw [windowDirection_getD_array _ W.length hlen,windowDirection_getD_array W W.length rfl]
  simp only [orderScalePairs_getD]
  exact conjugacyDirection_scalar _ _ _ c hc

/-- The genuine virtual gradient scales on every actual retained window. -/
theorem orderScalePairs_virtualGradient (c : ℝ) (hc : c≠0) (W : List (E × E)) (g : E) :
    virtualGradient (orderScalePairs c W) (c • g)=c • virtualGradient W g := by
  let s:=fun i : Fin W.length=>(W.getD i.val (0,0)).1
  let y:=fun i : Fin W.length=>(W.getD i.val (0,0)).2
  have hlen : (orderScalePairs c W).length=W.length := List.length_map _
  have hs : windowSteps (orderScalePairs c W)=(fun i=>c • s i) ∘ finCongr hlen := by
    rw [windowSteps_getD_array _ W.length hlen]
    simp only [orderScalePairs_getD,s]
  have hy : windowImages (orderScalePairs c W)=(fun i=>c • y i) ∘ finCongr hlen := by
    rw [windowImages_getD_array _ W.length hlen]
    simp only [orderScalePairs_getD,y]
  rw [(virtualWindow_coordinates _ hlen _ _ hs hy _).2,
    (virtualWindow_coordinates W rfl s y (windowSteps_getD_array W _ rfl) (windowImages_getD_array W _ rfl) g).2,
    pairModel_scalar,modelCoefficients_scalar s (pairModel s y) g c hc,combine_scalar,smul_add]

/-- True finite tilted coefficients have degree zero under common scaling. -/
theorem orderDeferredCoefficients_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s y : ι → E) (g : E) (a c : ℝ) (hc : c≠0) :
    deferredCoefficients (fun i=>c • s i) (fun i=>c • y i) (c • g) a=deferredCoefficients s y g a := by
  rw [deferredCoefficients,crossGram_scalar,coordinates_scalar,coordinates_scalar]
  have hrhs : (c*c) • coordinates y g-a⁻¹ • ((c*c) • coordinates s g)=
      (c*c) • (coordinates y g-a⁻¹ • coordinates s g) := by module
  rw [hrhs,matrix_inv_scalar,smul_mulVec,mulVec_smul,smul_smul,
    inv_mul_cancel₀ (mul_ne_zero hc hc),one_smul]
  rfl

/-- The actual finite deferred direction scales with its observed vectors. -/
theorem orderDeferredDirection_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s y : ι → E) (g : E) (a c : ℝ) (hc : c≠0) :
    deferredDirection (fun i=>c • s i) (fun i=>c • y i) (c • g) a=c • deferredDirection s y g a := by
  rw [deferredDirection,orderDeferredCoefficients_scalar s y g a c hc,combine_scalar,
    ←smul_neg,←smul_add]
  rfl

end
end krylov.Convergence
