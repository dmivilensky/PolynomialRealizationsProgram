import krylov.Methods.DirectionReindex
import krylov.Methods.ProjectedModel
import krylov.Methods.RepeatedCorrection

/-!
Article: main_krylov, lem:U(d), fixed finite coordinates for actual retained model solves.
Use: place actual full/sliding/restarted windows in a parameter-independent
finite coefficient space without changing any physical solve or observed pair.
Source: the existing actual chronological pair indexing and mathlib's inverse reindexing theorem.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A bijective relabeling of an actual model solve relabels its genuine computed coefficients.
Use: actual list-index inverses and fixed finite-coordinate inverses describe the same correction.
Article: main_krylov, lem:U(d), coefficient coordinates.
Proof: reindex the genuine totalized matrix inverse and change the finite right-hand-side summation index. -/
theorem modelCoefficients_reindex (e : κ ≃ ι) (s : ι → E) (H : Matrix ι ι ℝ) (g : E) (i : κ) :
    modelCoefficients (s ∘ e) (H.submatrix e e) g i=modelCoefficients s H g (e i) := by
  unfold modelCoefficients
  rw [Matrix.inv_submatrix_equiv]
  change -(∑ j, H⁻¹ (e i) (e j)*inner ℝ (s (e j)) g)=-(∑ j, H⁻¹ (e i) j*inner ℝ (s j) g)
  exact congrArg Neg.neg (Equiv.sum_comp e (fun j => H⁻¹ (e i) j*inner ℝ (s j) g))

/-- Every actual physical model correction is invariant under bijective relabeling of its window and model.
Use: regularity in fixed coordinates is regularity of the genuine computed physical correction.
Article: main_krylov, lem:U(d), actual finite model solve.
Proof: the actual coefficients relabel with their actual vectors and the physical finite sum is unchanged. -/
theorem modelCorrection_reindex (e : κ ≃ ι) (s : ι → E) (H : Matrix ι ι ℝ) (g : E) :
    combine (s ∘ e) (modelCoefficients (s ∘ e) (H.submatrix e e) g)=
      combine s (modelCoefficients s H g) := by
  unfold combine
  simp only [modelCoefficients_reindex,Function.comp_apply]
  exact Equiv.sum_comp e (fun i => modelCoefficients s H g i • s i)

omit [Fintype κ] [DecidableEq κ] in
/-- Actual inverse-Gram coefficients exactly synthesize every physical vector in the actual window span.
Use: coefficients of the new real recorded step are computed from genuine observed vectors.
Article: main_krylov, lem:projected-residual, bounded recorded-step coordinates.
Proof: represent the true span vector by a physical finite combination;
its actual coordinate equation cancels the genuine nonsingular Gram inverse. -/
theorem combine_gram_coordinates (s : ι → E) (v : E) (hu : IsUnit (crossGram s s).det)
    (hv : v∈Submodule.span ℝ (Set.range s)) : combine s (conjugacyCoefficients s s v)=v := by
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  change combine s c=v at hc
  rw [conjugacyCoefficients,← hc,coordinates_combine,mulVec_mulVec,nonsing_inv_mul _ hu,one_mulVec]

/-- Actual finite model-correction decision trees are invariant under bijective coefficient-coordinate changes.
Use: the real repeated-query execution can be differentiated in a fixed finite coordinate space.
Article: main_krylov, lem:U(d), actual RFC correction coordinates.
Proof: the actual first physical query is unchanged by model-solve invariance;
every possible returned gradient chooses the same recursively reindexed next tree. -/
theorem repeatedModelTree_reindex (e : κ ≃ ι) (s : ι → E) (H : Matrix ι ι ℝ)
    (count : ℕ) (g : E) :
    repeatedModelTree (s ∘ e) (H.submatrix e e) count g=repeatedModelTree s H count g := by
  induction count generalizing g with
  | zero => rfl
  | succ count ih =>
    simp only [repeatedModelTree,modelCorrection_reindex]
    congr 1
    exact funext ih

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
/-- A pure finite dimension cast preserves the genuine Euclidean spectral matrix norm.
Use: continuity of the real observed gate is checked on its fixed finite coordinate matrix.
Article: main_krylov, lem:U(d), observed defect gate.
Proof: equality elimination reduces the dimension cast to the identity map. -/
theorem spectral_norm_finCongr {a b : ℕ} (h : a=b) (M : Matrix (Fin b) (Fin b) ℝ) :
    ‖M.submatrix (finCongr h) (finCongr h)‖=‖M‖ := by
  subst b
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Every genuine retained transcript entry has its exact chronological step and observed secant.
Use: all retained-window coefficient arrays have fixed finite ages.
Article: main_krylov, lem:U(d), real retained observations.
Proof: taking the newest prefix preserves its indexed entry in the actual complete executed transcript. -/
theorem executedPairs_take_get (s y : ℕ → E) (k m : ℕ)
    (i : Fin ((executedPairs s y k).take m).length) :
    ((executedPairs s y k).take m).get i=(s (k-1-i.val),y (k-1-i.val)) := by
  have hi : i.val<k := by
    have ht := i.isLt
    simp only [List.length_take,executedPairs_length] at ht
    omega
  change ((executedPairs s y k).take m)[i.val]=_
  rw [List.getElem_take,executedPairs_get s y k i.val hi]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The actual retained steps and observed secants have their fixed finite-age coordinate families.
Use: reuse the exact same observed-data chart for direction, model, gate and correction estimates.
Article: main_krylov, lem:U(d), retained actual observation chart.
Proof: each family entry is the corresponding component of the proved actual retained chronological pair. -/
theorem retainedWindow_coordinates (s y : ℕ → E) (k m : ℕ) :
    let W := (executedPairs s y k).take m
    let h : W.length=min m k := by simp only [W,List.length_take,executedPairs_length]
    windowSteps W=(fun i : Fin (min m k) => s (k-1-i.val)) ∘ finCongr h ∧
      windowImages W=(fun i : Fin (min m k) => y (k-1-i.val)) ∘ finCongr h := by
  constructor
  · funext i
    exact congrArg Prod.fst (executedPairs_take_get s y k m i)
  · funext i
    exact congrArg Prod.snd (executedPairs_take_get s y k m i)

/-- The actual retained direction solve equals its fixed newest-age coordinate solve for every prescribed retention length.
Use: local regularity covers full, sliding and restarted windows through the same actual solve.
Article: main_krylov, lem:U(d), retained direction coordinates.
Proof: the actual retained length is min(m,k), each actual entry has its true
chronological age, and the proved physical conjugacy solve is invariant under the genuine index cast. -/
theorem windowDirection_executed_take (s y : ℕ → E) (g : E) (k m : ℕ) :
    windowDirection ((executedPairs s y k).take m) g=
      conjugacyDirection (fun i : Fin (min m k) => s (k-1-i.val))
        (fun i : Fin (min m k) => y (k-1-i.val)) g := by
  -- The finite coordinate type is determined by the retention rule and iteration count, not by parameter values.
  let W := (executedPairs s y k).take m
  let e : Fin W.length ≃ Fin (min m k) := finCongr (by simp only [W,List.length_take,executedPairs_length])
  have hs : windowSteps W=(fun i : Fin (min m k) => s (k-1-i.val)) ∘ e := by
    funext i
    exact congrArg Prod.fst (executedPairs_take_get s y k m i)
  have hy : windowImages W=(fun i : Fin (min m k) => y (k-1-i.val)) ∘ e := by
    funext i
    exact congrArg Prod.snd (executedPairs_take_get s y k m i)
  change conjugacyDirection (windowSteps W) (windowImages W) g=_
  rw [hs,hy,conjugacyDirection_reindex]

/-- The actual retained latest-information model is precisely its fixed newest-age model after the genuine index cast.
Use: analytic model entries and genuine model determinants refer to the real retained observations.
Article: main_krylov, lem:U(d), retained model coordinates.
Proof: the actual minimum and maximum indices select their exact observed
chronological pairs; the order-preserving finite length cast leaves these same ages unchanged. -/
theorem windowModel_executed_take (s y : ℕ → E) (k m : ℕ) :
    let W := (executedPairs s y k).take m
    let e : Fin W.length ≃ Fin (min m k) := finCongr (by simp only [W,List.length_take,executedPairs_length])
    windowModel W=(pairModel (fun i : Fin (min m k) => s (k-1-i.val))
      (fun i : Fin (min m k) => y (k-1-i.val))).submatrix e e := by
  -- The fixed model keeps the source's actual newest-information triangular convention.
  dsimp only
  ext i j
  have hs := congrArg Prod.fst (executedPairs_take_get s y k m (max i j))
  have hy := congrArg Prod.snd (executedPairs_take_get s y k m (min i j))
  change inner ℝ (windowSteps _ (max i j)) (windowImages _ (min i j))=_
  rw [show windowSteps _ (max i j)=s (k-1-(max i j).val) from hs,
    show windowImages _ (min i j)=y (k-1-(min i j).val) from hy]
  rfl

/-- Pure dimension casting preserves the actual latest-information model's index order.
Use: both actual newer/older indices survive conversion to fixed finite coordinates.
Article: main_krylov, lem:U(d), model coordinate covariance.
Proof: equality elimination turns the dimension cast into the identity. -/
theorem pairModel_finCongr {a b : ℕ} (h : a=b) (s y : Fin b → E) :
    pairModel (s ∘ finCongr h) (y ∘ finCongr h)=(pairModel s y).submatrix (finCongr h) (finCongr h) := by
  subst b
  rfl

/-- A genuine list model equals its fixed-coordinate latest model whenever its actual vectors have those coordinates.
Use: a single bridge handles retained, augmented and virtual actual model solves.
Article: main_krylov, lem:U(d), real model matrix coordinates.
Proof: the exact actual model is the latest pair model and pure dimension casting preserves its index order. -/
theorem windowModel_of_coordinates (W : List (E × E)) {b : ℕ} (h : W.length=b)
    (s y : Fin b → E) (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h) :
    windowModel W=(pairModel s y).submatrix (finCongr h) (finCongr h) := by
  rw [← pairModel_window,hs,hy]
  exact pairModel_finCongr h s y

/-- Genuine fixed coordinates preserve the actual observed conjugacy determinant.
Use: actual positive quadratic model domains justify the finite inverse in the analytic direction formula.
Article: main_krylov, lem:U(d), actual secant determinant domain.
Proof: both matrix axes use the same genuine coefficient index cast, whose determinant factors cancel. -/
theorem crossGram_det_of_coordinates (W : List (E × E)) {b : ℕ} (h : W.length=b)
    (s y : Fin b → E) (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h) :
    (crossGram (windowImages W) (windowSteps W)).det=(crossGram y s).det := by
  have he : crossGram (windowImages W) (windowSteps W)=
      (crossGram y s).submatrix (finCongr h) (finCongr h) := by rw [hs,hy]; rfl
  rw [he,Matrix.det_submatrix_equiv_self]

/-- The actual observed normalized skew-defect matrix in fixed finite vector coordinates.
Use: strict acceptance of the actual RFC gate follows from continuity of these genuine entries.
Article: main_krylov, alg:fc and lem:U(d), δ. -/
def pairDefect {b : ℕ} (s y : Fin b → E) : Matrix (Fin b) (Fin b) ℝ := fun i j =>
  (inner ℝ (s i) (y j)-inner ℝ (s j) (y i)) /
    Real.sqrt (inner ℝ (s i) (y i)*inner ℝ (s j) (y j))

/-- Genuine fixed coordinates preserve the actual RFC observed defect norm exactly.
Use: the strict gate is proved for the true observed data, with its real spectral norm.
Article: main_krylov, alg:fc and lem:U(d), actual observed gate.
Proof: the actual entry formula has precisely the fixed-coordinate vectors;
its matrix is a pure dimension cast, which preserves the genuine spectral norm. -/
theorem windowDefect_norm_of_coordinates (W : List (E × E)) {b : ℕ} (h : W.length=b)
    (s y : Fin b → E) (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h) :
    ‖windowDefect W‖=‖pairDefect s y‖ := by
  have he : windowDefect W=(pairDefect s y).submatrix (finCongr h) (finCongr h) := by
    ext i j
    simp only [windowDefect,hs,hy,pairDefect,submatrix_apply,Function.comp_apply]
  rw [he]
  exact spectral_norm_finCongr h _

/-- The genuine repeated model tree has exactly its fixed-coordinate physical decision tree.
Use: actual model inverses and all actually observed correction right-hand sides retain their meaning after reindexing.
Article: main_krylov, lem:U(d), real repeated-query coordinates.
Proof: identify the actual model matrix and actual vectors under their pure
dimension cast, then apply physical invariance of the entire finite decision tree. -/
theorem repeatedModelTree_window_coordinates (W : List (E × E)) {b : ℕ} (h : W.length=b)
    (s y : Fin b → E) (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h)
    (count : ℕ) (g : E) :
    repeatedModelTree (windowSteps W) (windowModel W) count g=repeatedModelTree s (pairModel s y) count g := by
  rw [windowModel_of_coordinates W h s y hs hy,hs]
  exact repeatedModelTree_reindex (finCongr h) s (pairModel s y) count g

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Actual augmented retained step and image families have their exact fixed current-plus-age coordinates.
Use: the RFC model inverse contains the real current direction and real probe beside the true retained observations.
Article: main_krylov, lem:U(d), augmented U=[S,d] and current probe.
Proof: the actual head gives the new direction/probe; every successor index
selects its proved chronological retained pair through the same pure dimension cast. -/
theorem augmentedWindow_coordinates (s y : ℕ → E) (k m : ℕ) (d z : E) :
    let W := (d,z)::(executedPairs s y k).take m
    let h : W.length=min m k+1 := by simp only [W,List.length_cons,List.length_take,executedPairs_length]
    windowSteps W=(Fin.cons d (fun i : Fin (min m k) => s (k-1-i.val))) ∘ finCongr h ∧
      windowImages W=(Fin.cons z (fun i : Fin (min m k) => y (k-1-i.val))) ∘ finCongr h := by
  -- The head and every real retained old pair are identified before touching the actual model inverse.
  dsimp only
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change windowSteps ((executedPairs s y k).take m) j=s (k-1-j.val)
      exact congrArg Prod.fst (executedPairs_take_get s y k m j)
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change windowImages ((executedPairs s y k).take m) j=y (k-1-j.val)
      exact congrArg Prod.snd (executedPairs_take_get s y k m j)

end
end krylov.Methods
