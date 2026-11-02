import krylov.Tensor.BinaryFibreRegularity
import krylov.Tensor.CubicBanach
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: main_krylov, apD:lem-binary(a,d) and thm:Fplanar.
Use: identify the actual symmetric binary tensor, prove the sharp mixed
coefficient disk bounds from its diagonal norm, and derive the RFC-F upper
bound. Source: Banach's theorem, proved in CubicBanach, and planar
Cauchy--Schwarz; no coefficient bounds are supplied as assumptions.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open krylov.Functions

/-- The real Hilbert plane carrying the actual binary tensor.
Article: main_krylov, apD:lem-binary. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Pin the iterated operator-space instance to avoid exponential synthesis
-- through three curried continuous-linear-map codomains.
local instance : NormedAddCommGroup (Plane →L[ℝ] Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Plane) (F := Plane →L[ℝ] Plane →L[ℝ] ℝ)

/-- A coordinate tensor product represented by genuine continuous linear maps.
Article: main_krylov, apD:lem-binary. -/
def tensorMonomial (i j k : Fin 2) : Plane →L[ℝ] Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight (EuclideanSpace.proj k))

/-- The genuine symmetric trilinear form with the four prescribed coefficients.
Article: main_krylov, apD:lem-binary. -/
def tensor (t : BinaryCubic) : SymmetricCubic Plane where
  form := t.t0 • tensorMonomial 0 0 0+
    t.t1 • (tensorMonomial 0 0 1+tensorMonomial 0 1 0+tensorMonomial 1 0 0)+
    t.t2 • (tensorMonomial 0 1 1+tensorMonomial 1 0 1+tensorMonomial 1 1 0)+
    t.t3 • tensorMonomial 1 1 1
  swap₁ := by
    intro a b c
    simp only [tensorMonomial,ContinuousLinearMap.smulRight_apply,add_apply,smul_apply,
      smul_eq_mul,EuclideanSpace.coe_proj]
    ring
  swap₂ := by
    intro a b c
    simp only [tensorMonomial,ContinuousLinearMap.smulRight_apply,add_apply,smul_apply,
      smul_eq_mul,EuclideanSpace.coe_proj]
    ring

/-- Evaluation of the actual tensor in binary coordinates.
Article: main_krylov, apD:lem-binary. -/
theorem tensor_apply (t : BinaryCubic) (x y z : Plane) :
    t.tensor.form x y z=t.t0*x 0*y 0*z 0+
      t.t1*(x 0*y 0*z 1+x 0*y 1*z 0+x 1*y 0*z 0)+
      t.t2*(x 0*y 1*z 1+x 1*y 0*z 1+x 1*y 1*z 0)+t.t3*x 1*y 1*z 1 := by
  simp only [tensor,tensorMonomial,ContinuousLinearMap.smulRight_apply,add_apply,smul_apply,
    smul_eq_mul,EuclideanSpace.coe_proj]
  ring

/-- The tensor's diagonal is exactly the polynomial defining the original ball.
Article: main_krylov, apD:lem-binary. -/
theorem tensor_diagonal (t : BinaryCubic) (x : Plane) :
    t.tensor.form x x x=t.eval (x 0) (x 1) := by
  rw [tensor_apply]
  unfold eval
  ring

/-- The norm of a real Hilbert-plane vector is the actual coordinate radius.
Article: main_krylov, apD:lem-binary. -/
theorem plane_norm_sq (x : Plane) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x

/-- Every binary cubic in the actual diagonal ball obeys the full mixed
Banach estimate on its true tensor.
Article: main_krylov, apD:lem-binary(a). -/
theorem tensor_bound {t : BinaryCubic} (ht : t.InBall) (x y z : Plane) :
    |t.tensor.form x y z|≤‖x‖*‖y‖*‖z‖ := by
  have hdiag : ∀ u : Plane, ‖u‖=1 → |t.tensor.form u u u|≤1 := by
    intro u hu
    rw [tensor_diagonal]
    exact ht _ _ (by have h := plane_norm_sq u;rw [hu] at h;nlinarith)
  simpa only [one_mul] using cubic_diagonal_bound t.tensor 1 hdiag x y z

/-- The two sharp coefficient disk constraints follow from the actual
mixed tensor estimate, including all degenerate coefficient vectors.
Article: main_krylov, apD:lem-binary(a). -/
theorem coefficient_disks {t : BinaryCubic} (ht : t.InBall) :
    t.t0^2+t.t1^2≤1 ∧ t.t1^2+t.t2^2≤1 := by
  let e0 : Plane := WithLp.toLp 2 ![1,0]
  let e1 : Plane := WithLp.toLp 2 ![0,1]
  have he0 : ‖e0‖=1 := by
    have h : ‖e0‖^2=1 := by rw [plane_norm_sq];norm_num [e0]
    nlinarith [norm_nonneg e0]
  have he1 : ‖e1‖=1 := by
    have h : ‖e1‖^2=1 := by rw [plane_norm_sq];norm_num [e1]
    nlinarith [norm_nonneg e1]
  constructor
  · let v : Plane := WithLp.toLp 2 ![t.t0,t.t1]
    have h := tensor_bound ht e0 e0 v
    rw [he0,one_mul,one_mul] at h
    have he : t.tensor.form e0 e0 v=t.t0^2+t.t1^2 := by
      simp [tensor_apply,e0,v,pow_two]
    have hv : ‖v‖^2=t.t0^2+t.t1^2 := by simpa [v] using plane_norm_sq v
    rw [he,abs_of_nonneg (by positivity)] at h
    have hn : ‖v‖≤1 := by nlinarith
    nlinarith [norm_nonneg v]
  · let v : Plane := WithLp.toLp 2 ![t.t1,t.t2]
    have h := tensor_bound ht e0 e1 v
    rw [he0,he1,one_mul,one_mul] at h
    have he : t.tensor.form e0 e1 v=t.t1^2+t.t2^2 := by
      simp [tensor_apply,e0,e1,v,pow_two]
    have hv : ‖v‖^2=t.t1^2+t.t2^2 := by simpa [v] using plane_norm_sq v
    rw [he,abs_of_nonneg (by positivity)] at h
    have hn : ‖v‖≤1 := by nlinarith
    nlinarith [norm_nonneg v]

/-- The actual leading RFC-F binary objective.
Article: main_krylov, apD:lem-binary(d) and thm:Fplanar. -/
def rfcObjective (r : ℝ) (t : BinaryCubic) : ℝ :=
  |t.t1+r*t.t2| * Real.sqrt (4*t.t1^2+t.t2^2)

/-- The printed sharp upper envelope for every admissible actual binary cubic.
Article: main_krylov, apD:lem-binary(d).
Proof: the proved coefficient disk gives both planar Cauchy--Schwarz
and the bound of two on the second factor. -/
theorem rfcObjective_le {t : BinaryCubic} (ht : t.InBall) (r : ℝ) :
    rfcObjective r t≤2*Real.sqrt (1+r^2) := by
  have hd := (coefficient_disks ht).2
  have hroot : Real.sqrt (4*t.t1^2+t.t2^2)≤2 := by
    have hsq := Real.sq_sqrt (by positivity : 0≤4*t.t1^2+t.t2^2)
    nlinarith [Real.sqrt_nonneg (4*t.t1^2+t.t2^2),sq_nonneg t.t2]
  have hpair : |t.t1+r*t.t2|≤Real.sqrt (1+r^2) := by
    have hsq := Real.sq_sqrt (by positivity : 0≤1+r^2)
    have hdot : (t.t1+r*t.t2)^2≤1+r^2 := by
      have h := mul_le_mul_of_nonneg_left hd (by positivity : 0≤1+r^2)
      nlinarith [sq_nonneg (r*t.t1-t.t2)]
    nlinarith [sq_abs (t.t1+r*t.t2),abs_nonneg (t.t1+r*t.t2),Real.sqrt_nonneg (1+r^2)]
  unfold rfcObjective
  have h := mul_le_mul hpair hroot (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The harmonic sine cubic appearing in the printed lower bound.
Article: main_krylov, apD:lem-binary(d), sin(3phi). -/
def harmonicSine : BinaryCubic := ⟨0,1,0,-1⟩

/-- The harmonic cubic is genuinely admissible in the diagonal norm.
Article: main_krylov, apD:lem-binary(d).
Proof: its homogeneous squared gap is c²(c²−3s²)². -/
theorem harmonicSine_inBall : harmonicSine.InBall := by
  intro c s hcs
  have he : (c^2+s^2)^3-(harmonicSine.eval c s)^2=c^2*(c^2-3*s^2)^2 := by
    simp only [eval,harmonicSine]
    ring
  have hp := mul_nonneg (sq_nonneg c) (sq_nonneg (c^2-3*s^2))
  rw [hcs,one_pow] at he
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (harmonicSine.eval c s+1),sq_nonneg (harmonicSine.eval c s-1)]

/-- The harmonic cubic has objective exactly two for every shear parameter.
Article: main_krylov, apD:lem-binary(d). -/
theorem harmonicSine_rfcObjective (r : ℝ) : rfcObjective r harmonicSine=2 := by
  norm_num [rfcObjective,harmonicSine]

end
end krylov.Tensor.BinaryCubic
