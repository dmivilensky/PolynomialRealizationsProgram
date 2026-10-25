import polyak.Numerics.Parametric.Contract
import polyak.Numerics.Parametric.Memo

/-! Article: Appendix B, checked enclosures for the actual differentiated
implicit equations. The preconditioner is a proposal; its norm defect proves
the bound on every actual solution, without assuming an inverse matrix. -/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine
open scoped Matrix.Norms.Operator

local instance : Zero IntervalRat := ⟨IntervalRat.singleton 0⟩
local instance : Add IntervalRat := ⟨IntervalRat.add⟩
local instance : SMul ℕ IntervalRat where
  smul n a := ⟨(n : ℚ)*a.lo,(n : ℚ)*a.hi,
    mul_le_mul_of_nonneg_left a.le (by positivity)⟩
local instance : AddCommMonoid IntervalRat :=
  Function.Injective.addCommMonoid (fun I : IntervalRat => (I.lo,I.hi))
    (by intro a b h; cases a; cases b; simp_all) rfl (fun _ _ => rfl) (fun _ _ => rfl)

def linearScaledJacobian {n : ℕ} (J : Matrix (Fin n) (Fin n) IntervalRat)
    (r : Fin n → ℚ) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => IntervalRat.scale (r j) (J i j)

def linearScaledInverse {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ)
    (r : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ := fun i j => Y i j/r i

def linearCenterResidual {n : ℕ} (J : Matrix (Fin n) (Fin n) IntervalRat)
    (p : Fin n → IntervalRat) (a : Fin n → ℚ) : Fin n → IntervalRat :=
  fun i => (p i).add (Finset.univ.sum fun j => IntervalRat.scale (a j) (J i j))

def linearConstant {n : ℕ} (J : Matrix (Fin n) (Fin n) IntervalRat)
    (p : Fin n → IntervalRat) (a r : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) : Fin n → IntervalRat :=
  let residual:=memoFin (linearCenterResidual J p a)
  memoFin (fun i => IntervalRat.neg (intervalRatMatVec (linearScaledInverse Y r) residual i))

def linearSolutionCheck {n : ℕ} (J : Matrix (Fin n) (Fin n) IntervalRat)
    (p : Fin n → IntervalRat) (a r : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (q : ℚ) : Bool :=
  let defect:=memoMatrix (preconditionedJacobian (linearScaledInverse Y r)
    (linearScaledJacobian J r))
  let residual:=memoFin (linearConstant J p a r Y)
  decide (∀ i,0<r i) && decide (q<1) &&
    decide (intervalMatrixBound defect≤q) &&
      decide (∀ i,intervalAbsBound (residual i)≤1-q)

noncomputable section

theorem linearSolutionCheck_sound {n : ℕ}
    (J : Matrix (Fin n) (Fin n) IntervalRat) (p : Fin n → IntervalRat)
    (a r : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (q : ℚ)
    (hc : linearSolutionCheck J p a r Y q=true)
    (D : Matrix (Fin n) (Fin n) ℝ) (b v : Fin n → ℝ)
    (hD : ∀ i j,D i j∈J i j) (hb : ∀ i,b i∈p i)
    (hv : D.mulVec v= -b) : FinBoxMem v (coordinateBox a r) := by
  simp only [linearSolutionCheck,memoMatrix_eq,memoFin_eq,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hr,hq⟩,hdefect⟩,hC⟩:=hc
  let R:=(linearScaledInverse Y r).map (fun q => (q : ℝ))
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => D i j*(r j : ℝ)
  let z : Fin n → ℝ := fun i => (v i-(a i : ℝ))/(r i : ℝ)
  let c : Fin n → ℝ := -(R.mulVec (b+D.mulVec (fun i => (a i : ℝ))))
  let M : Matrix (Fin n) (Fin n) ℝ := 1-R*A
  have hA : ∀ i j,A i j∈linearScaledJacobian J r i j := by
    intro i j
    simpa only [A,linearScaledJacobian,mul_comm] using IntervalRat.mem_scale (r j) (hD i j)
  have hM : ‖M‖≤(q : ℝ) := (matrix_norm_le_intervalMatrixBound _ _
    (mem_preconditionedJacobian (linearScaledInverse Y r) A _ hA)).trans (by exact_mod_cast hdefect)
  have hcMem (i : Fin n) : c i∈linearConstant J p a r Y i := by
    simp only [linearConstant,memoFin_eq]
    apply IntervalRat.mem_neg
    apply mem_interval_sum Finset.univ
      (fun j => (linearScaledInverse Y r i j : ℝ)*(b+D.mulVec (fun i => (a i : ℝ))) j)
      (fun j => IntervalRat.scale (linearScaledInverse Y r i j) (linearCenterResidual J p a j))
    intro j _
    apply IntervalRat.mem_scale
    apply IntervalRat.mem_add (hb j)
    have hh:=mem_interval_sum Finset.univ
      (fun k => (a k : ℝ)*D j k) (fun k => IntervalRat.scale (a k) (J j k))
      (fun k _ => IntervalRat.mem_scale (a k) (hD j k))
    simpa only [Matrix.mulVec,dotProduct,mul_comm] using hh
  have hcNorm : ‖c‖≤1-(q : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast (sub_nonneg.mpr hq.le))).mpr
    intro i
    exact (abs_le_intervalAbsBound (hcMem i)).trans (by exact_mod_cast hC i)
  have hAz : A.mulVec z= -b-D.mulVec (fun i => (a i : ℝ)) := by
    have he : A.mulVec z=D.mulVec (v-(fun i => (a i : ℝ))) := by
      ext i
      simp only [Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      have hri : (r j : ℝ)≠0 := by exact_mod_cast (hr j).ne'
      dsimp [A,z]
      field_simp
    rw [he,Matrix.mulVec_sub,hv]
  have hz : z=M.mulVec z+c := by
    dsimp only [M,c]
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,←Matrix.mulVec_mulVec,hAz]
    simp only [Matrix.mulVec_sub,Matrix.mulVec_neg,Matrix.mulVec_add]
    ext i
    simp only [Pi.neg_apply,Pi.sub_apply,Pi.add_apply]
    ring
  have hzNorm : ‖z‖≤1 := by
    have hh : ‖z‖≤‖M‖*‖z‖+‖c‖ := by
      calc
        ‖z‖=‖M.mulVec z+c‖ := congrArg norm hz
        _≤‖M.mulVec z‖+‖c‖ := norm_add_le _ _
        _≤‖M‖*‖z‖+‖c‖ := add_le_add (Matrix.linfty_opNorm_mulVec _ _) le_rfl
    have hh' : ‖z‖≤(q : ℝ)*‖z‖+(1-(q : ℝ)) :=
      hh.trans (add_le_add (mul_le_mul_of_nonneg_right hM (norm_nonneg z)) hcNorm)
    have hqp : (q : ℝ)<1 := by exact_mod_cast hq
    nlinarith
  have hzBox : FinBoxMem z (unitBox n) := by
    intro i
    have hh : |z i|≤1 := (norm_le_pi_norm z i).trans hzNorm
    simpa only [unitBox,IntervalRat.mem_def,Rat.cast_neg,Rat.cast_one] using abs_le.mp hh
  have hchart:=chart_mem a r hr hzBox
  have he : chart a r z=v := by
    ext i
    have hri : (r i : ℝ)≠0 := by exact_mod_cast (hr i).ne'
    dsimp [chart,z]
    field_simp
    ring
  rwa [he] at hchart

end
end polyak.Numerics.Parametric
