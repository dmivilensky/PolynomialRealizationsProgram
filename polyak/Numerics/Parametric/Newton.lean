import polyak.Numerics.Parametric.Basic

/-!
Article: Appendix B, uniform unknown-coordinate Jacobian bounds.
Use: the interval parameter remains free while the Newton contraction acts
only on the unknown coordinates.  All norm bounds concern the actual derivative.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine
open scoped Matrix.Norms.Operator

def newton {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (F : Fin n → Expr)
    (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := x-Y.mulVec (system F s x)

theorem newton_differentiable {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (s : ℝ) :
    Differentiable ℝ (newton Y F s) := by
  have hY : Differentiable ℝ (fun x => matrixCLM Y (system F s x)) :=
    (matrixCLM Y).differentiable.comp (system_differentiable F h s)
  exact differentiable_id.sub hY

theorem newton_fderiv_matrix {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (s : ℝ) (x : Fin n → ℝ) :
    LinearMap.toMatrix' (fderiv ℝ (newton Y F s) x).toLinearMap=1-Y*jacobian F s x := by
  have hF := (system_differentiable F h s).differentiableAt.hasFDerivAt (x := x)
  have hY := (matrixCLM Y).hasFDerivAt.comp x hF
  have hg : HasFDerivAt (newton Y F s)
      (ContinuousLinearMap.id ℝ _-(matrixCLM Y).comp (fderiv ℝ (system F s) x)) x :=
    (hasFDerivAt_id x).sub hY
  rw [hg.fderiv]
  rw [ContinuousLinearMap.toLinearMap_sub]
  change LinearMap.toMatrix' (1-(matrixCLM Y).toLinearMap.comp
    (fderiv ℝ (system F s) x).toLinearMap)=_
  rw [map_sub,LinearMap.toMatrix'_one,LinearMap.toMatrix'_comp]
  have hmat : LinearMap.toMatrix' (matrixCLM Y).toLinearMap=Y :=
    LinearMap.toMatrix'_toLin' Y
  rw [hmat]
  rfl

theorem newton_fderiv_norm_le {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (I : IntervalRat)
    (X : Fin n → IntervalRat) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) (cfg : EvalConfig) :
    ‖fderiv ℝ (newton (Y.map fun q => (q : ℝ)) F s) x‖≤
      (intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg)) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix,newton_fderiv_matrix _ F h]
  apply matrix_norm_le_intervalMatrixBound
  exact mem_preconditionedJacobian Y (jacobian F s x) (intervalJacobian F I X cfg)
    (jacobian_mem F h I X hs hx cfg)

theorem fixedPoint_iff_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (hdet : Y.det≠0) (s : ℝ) (x : Fin n → ℝ) :
    newton (Y.map fun q => (q : ℝ)) F s x=x ↔ system F s x=0 := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun q => (q : ℝ)
  have hdetR : Yr.det≠0 := by
    dsimp [Yr]
    exact_mod_cast hdet
  have hinj : Function.Injective Yr.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero hdetR
  constructor
  · intro hfix
    apply hinj
    have hm : Yr.mulVec (system F s x)=0 := by
      have he := congrArg (fun y => x-y) hfix
      simpa [newton,Yr] using he
    simpa using hm
  · intro hz
    simp [newton,hz]

theorem unique_root_of_uniform_bounds {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (I : IntervalRat)
    (X : Fin n → IntervalRat) (m : Fin n → ℝ) (hm : FinBoxMem m X)
    (hdet : Y.det≠0) (cfg : EvalConfig)
    (hq : intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg))<1)
    (hmap : ∀ s∈I, Set.MapsTo (newton (Y.map fun q => (q : ℝ)) F s)
      (finBoxSet X) (finBoxSet X)) :
    ∀ s∈I, ∃! x, FinBoxMem x X ∧ system F s x=0 := by
  intro s hs
  let q := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F I X cfg))
  have hq0 : 0≤q := by
    dsimp [q,intervalMatrixBound]
    generalize (List.ofFn fun i => intervalMatrixRowBound
      (preconditionedJacobian Y (intervalJacobian F I X cfg)) i)=l
    have hl : ∀ (l : List ℚ) (a : ℚ), a≤l.foldl max a := by
      intro l
      induction l with
      | nil => intro a; exact le_rfl
      | cons b l ih => intro a; exact (le_max_left a b).trans (ih _)
    exact hl l 0
  have he := contraction_unique_fixedPoint_in_finBox X m hm
    (newton (Y.map fun q => (q : ℝ)) F s) (hmap s hs) (q : ℝ)
    (by exact_mod_cast hq0) (by exact_mod_cast hq)
    (fun x _ => (newton_differentiable _ F h s).differentiableAt)
    (fun _ hx => newton_fderiv_norm_le Y F h I X hs hx cfg)
  obtain ⟨x,hx,huniq⟩ := he
  refine ⟨x,⟨hx.1,(fixedPoint_iff_zero Y F hdet s x).mp hx.2⟩,?_⟩
  intro y hy
  exact huniq y ⟨hy.1,(fixedPoint_iff_zero Y F hdet s y).mpr hy.2⟩

end polyak.Numerics.Parametric
