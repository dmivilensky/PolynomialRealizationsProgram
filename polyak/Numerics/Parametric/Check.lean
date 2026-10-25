import polyak.Numerics.Parametric.Newton
import polyak.Numerics.Parametric.Residual

/-!
Article: Appendix B, a parametric interval Krawczyk check.
Use: one finite rational check proves a unique zero for every real parameter
in its closed slab. Certificate data contain no asserted numerical conclusions.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def centerValues {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  centerResidual F I m cfg

noncomputable section

theorem centerValues_mem {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (m : Fin n → ℚ) {s : ℝ} (hs : s∈I) (cfg : EvalConfig) (i : Fin n) :
    system F s (fun j => (m j : ℝ)) i∈centerValues F I m cfg i := by
  exact centerResidual_mem F h I m hs cfg i

end

def centerImage {n : ℕ} (F : Fin n → Expr) (I : IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => IntervalRat.sub (IntervalRat.singleton (m i))
    (intervalRatMatVec Y (centerValues F I m cfg) i)

def image {n : ℕ} (F : Fin n → Expr) (I : IntervalRat) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) :
    Fin n → IntervalRat :=
  let q := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg))
  fun i => IntervalRat.add (centerImage F I m Y cfg i) (symmetricInterval (q*boxRadius X m))

structure Certificate (n : ℕ) where
  center : Fin n → ℚ
  preconditioner : Matrix (Fin n) (Fin n) ℚ

def check {n : ℕ} (F : Fin n → Expr) (I : IntervalRat) (X : Fin n → IntervalRat)
    (cert : Certificate n) (cfg : EvalConfig := {}) : Bool :=
  decide (∀ i, (F i).checkADSupported=true) &&
  decide (centerInside X cert.center) && decide (cert.preconditioner.det≠0) &&
  decide (intervalMatrixBound (preconditionedJacobian cert.preconditioner
    (intervalJacobian F I X cfg))<1) &&
  decide (∀ i, intervalStrictInside (image F I X cert.center cert.preconditioner cfg i) (X i)=true)

noncomputable section

theorem matrixBound_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) IntervalRat) :
    0 ≤ intervalMatrixBound A := by
  unfold intervalMatrixBound
  generalize (List.ofFn fun i => intervalMatrixRowBound A i)=l
  have hl : ∀ (l : List ℚ) (a : ℚ), a≤l.foldl max a := by
    intro l
    induction l with
    | nil => intro a; exact le_rfl
    | cons b l ih => intro a; exact (le_max_left a b).trans (ih _)
  exact hl l 0

theorem centerImage_mem {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    {s : ℝ} (hs : s∈I) (cfg : EvalConfig) (i : Fin n) :
    newton (Y.map fun q => (q : ℝ)) F s (fun j => (m j : ℝ)) i∈centerImage F I m Y cfg i := by
  apply IntervalRat.mem_sub (IntervalRat.mem_singleton (m i))
  exact mem_interval_sum Finset.univ
    (fun j => (Y i j : ℝ)*system F s (fun k => (m k : ℝ)) j)
    (fun j => IntervalRat.scale (Y i j) (centerValues F I m cfg j))
    (fun j _ => IntervalRat.mem_scale (Y i j) (centerValues_mem F h I m hs cfg j))

theorem newton_mem_image {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun j => (m j : ℝ)) X) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) {s : ℝ} (hs : s∈I) {x : Fin n → ℝ}
    (hx : FinBoxMem x X) (i : Fin n) :
    newton (Y.map fun q => (q : ℝ)) F s x i∈image F I X m Y cfg i := by
  let q := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg))
  let mr : Fin n → ℝ := fun j => (m j : ℝ)
  have hd : ‖newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr‖≤(q : ℝ)*‖x-mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · exact fun _ _ => (newton_differentiable _ F h s).differentiableAt
    · exact fun _ hz => newton_fderiv_norm_le Y F h I X hs hz cfg
    · exact hm
    · exact hx
  have hq0 : 0≤q := matrixBound_nonneg _
  have hnorm : ‖newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr‖≤((q*boxRadius X m : ℚ) : ℝ) := by
    calc
      _≤(q : ℝ)*‖x-mr‖ := hd
      _≤(q : ℝ)*(boxRadius X m : ℝ) := mul_le_mul_of_nonneg_left
        (norm_sub_center_le_boxRadius hx) (by exact_mod_cast hq0)
      _=_ := by push_cast; rfl
  have hc : |(newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr) i|≤((q*boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr : (newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr) i∈symmetricInterval (q*boxRadius X m) := by
    rw [abs_le] at hc
    simpa [symmetricInterval,IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 (boxRadius_nonneg X m))] using hc
  have hm' := IntervalRat.mem_add (centerImage_mem F h I m Y hs cfg i) herr
  simpa [image,q,mr,Pi.sub_apply] using hm'

theorem newton_mapsTo {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun j => (m j : ℝ)) X) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig)
    (hi : ∀ i, intervalStrictInside (image F I X m Y cfg i) (X i)=true)
    {s : ℝ} (hs : s∈I) :
    Set.MapsTo (newton (Y.map fun q => (q : ℝ)) F s) (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  exact intervalStrictInside_sound (hi i) _ (newton_mem_image F h I X m hm Y cfg hs hx i)

theorem check_sound {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cert : Certificate n) (cfg : EvalConfig)
    (hc : check F I X cert cfg=true) :
    ∀ s∈I, ∃! x, FinBoxMem x X ∧ system F s x=0 := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hF,hm⟩,hdet⟩,hq⟩,hi⟩ := hc
  have h : ∀ i, ADSupported (F i) := fun i => ((F i).checkADSupported_eq_true_iff).mp (hF i)
  exact unique_root_of_uniform_bounds cert.preconditioner F h I X
    (fun j => (cert.center j : ℝ)) (centerInside_sound hm) hdet cfg hq
    (fun _ hs => newton_mapsTo F h I X cert.center (centerInside_sound hm)
      cert.preconditioner cfg hi hs)

end
end polyak.Numerics.Parametric
