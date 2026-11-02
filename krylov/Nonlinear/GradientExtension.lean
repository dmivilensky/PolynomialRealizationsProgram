import krylov.LinearAlgebra.SymmetricBall
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

/-!
Article: main_krylov, thm:RFCS, genuine nonlinear localization extension.
Use: Extend a local gradient error globally with a controlled finite-dimensional
Lipschitz bound, preserving every genuine local gradient value. Represent its
actual total-step and nonzero finite-probe secants by genuinely self-adjoint
operators uniformly close to the true fixed quadratic reference.
Source: McShane's scalar Lipschitz extension, mathlib
LipschitzOnWith.extend_real, finite Euclidean Cauchy--Schwarz, and the already
proved exact self-adjoint backward-error ball (Rump03, Lemma 5.1).
-/

namespace krylov.Nonlinear
noncomputable section
open Set
open scoped NNReal InnerProductSpace

/-- Every genuine local finite-dimensional Euclidean Lipschitz map has a global extension preserving its actual local values with the explicit square-root-dimension Lipschitz factor.
Use: Derive global auxiliary oracle control before proving localization of the genuine nonlinear RFC-S queries.
Article: main_krylov, thm:RFCS, actual gradient-extension and secant representation.
Proof: Extend the genuine scalar coordinates or apply the proved exact self-adjoint image-ball theorem to the real measured gradient difference.
-/
theorem exists_euclidean_lipschitz_extension {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (f : X → EuclideanSpace ℝ (Fin n)) {S : Set X} {K : ℝ≥0} (hf : LipschitzOnWith K f S) :
    ∃ g : X → EuclideanSpace ℝ (Fin n), LipschitzWith (NNReal.sqrt n*K) g ∧ EqOn f g S := by
  -- Extend actual scalar coordinates separately, then sum their genuine squared Lipschitz bounds to recover the explicit Euclidean dimension factor.
  have hcoord (i : Fin n) : LipschitzOnWith K (fun x => f x i) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := PiLp.norm_apply_le (f x-f y) i
    have hp : dist (f x i) (f y i)≤dist (f x) (f y) := by simpa only [dist_eq_norm,WithLp.ofLp_sub,Pi.sub_apply] using h
    exact hp.trans (hf.dist_le_mul x hx y hy)
  choose φ hφ heq using fun i => (hcoord i).extend_real
  let g := fun x => WithLp.toLp 2 (fun i => φ i x)
  refine ⟨g,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp only [EuclideanSpace.real_norm_sq_eq,NNReal.coe_mul,Real.coe_sqrt,NNReal.coe_natCast]
    simp only [WithLp.ofLp_sub,Pi.sub_apply]
    change (∑ i, (φ i x-φ i y)^2)≤(Real.sqrt n*(K : ℝ)*dist x y)^2
    calc
      _ ≤ ∑ _i : Fin n, ((K : ℝ)*dist x y)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := (hφ i).dist_le_mul x y
        rw [dist_eq_norm,Real.norm_eq_abs] at h
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
      _ = (n : ℝ)*((K : ℝ)*dist x y)^2 := by simp
      _ = _ := by simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; ring
  · intro x hx
    ext i
    exact heq i hx


/-- Every genuine locally Lipschitz gradient error around its fixed quadratic model has a global model-error Lipschitz extension preserving all original gradient values on their actual local domain.
Use: Derive global auxiliary oracle control before proving localization of the genuine nonlinear RFC-S queries.
Article: main_krylov, thm:RFCS, actual gradient-extension and secant representation.
Proof: Extend the genuine scalar coordinates or apply the proved exact self-adjoint image-ball theorem to the real measured gradient difference.
-/
theorem exists_gradient_model_extension {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} {K : ℝ≥0}
    (hG : LipschitzOnWith K (fun x => G x-Q x) S) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), EqOn G H S ∧
      LipschitzWith (NNReal.sqrt n*K) (fun x => H x-Q x) := by
  obtain ⟨F,hF,heq⟩ := exists_euclidean_lipschitz_extension (fun x => G x-Q x) hG
  refine ⟨fun x => Q x+F x,?_,?_⟩
  · intro x hx
    change G x=Q x+F x
    rw [← heq hx]
    module
  · simpa only [add_sub_cancel_left] using hF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual full gradient-difference secant of a globally controlled gradient error is the action of a genuinely self-adjoint operator with the same uniform perturbation bound, including a zero total step.
Use: Derive global auxiliary oracle control before proving localization of the genuine nonlinear RFC-S queries.
Article: main_krylov, thm:RFCS, actual gradient-extension and secant representation.
Proof: Extend the genuine scalar coordinates or apply the proved exact self-adjoint image-ball theorem to the real measured gradient difference.
-/
theorem exists_selfAdjoint_secant_of_lipschitz_error (G : E → E) (Q : E →L[ℝ] E)
    (hQ : IsSelfAdjoint Q) {K : ℝ≥0} (hG : LipschitzWith K (fun x => G x-Q x)) (x u : E) :
    ∃ A : E →L[ℝ] E, IsSelfAdjoint A ∧ ‖A-Q‖≤(K : ℝ) ∧ A u=G (x+u)-G x := by
  have hw : ‖(G (x+u)-Q (x+u))-(G x-Q x)‖≤(K : ℝ)*‖u‖ := by
    simpa only [add_sub_cancel_left] using hG.norm_sub_le (x+u) x
  obtain ⟨T,hT,hbound,himage⟩ := krylov.LinearAlgebra.exists_selfAdjoint_image u _ K.2 hw
  refine ⟨Q+T,hQ.add hT,?_,?_⟩
  · rw [add_sub_cancel_left]
    exact hbound
  · rw [_root_.add_apply,himage,map_add]
    abel

/-- Every genuine nonzero finite gradient probe has a true self-adjoint operator representative with a length-independent perturbation bound around its original quadratic reference.
Use: Derive global auxiliary oracle control before proving localization of the genuine nonlinear RFC-S queries.
Article: main_krylov, thm:RFCS, actual gradient-extension and secant representation.
Proof: Extend the genuine scalar coordinates or apply the proved exact self-adjoint image-ball theorem to the real measured gradient difference.
-/
theorem exists_selfAdjoint_probe_of_lipschitz_error (G : E → E) (Q : E →L[ℝ] E)
    (hQ : IsSelfAdjoint Q) {K : ℝ≥0} (hG : LipschitzWith K (fun x => G x-Q x))
    (x d : E) {h : ℝ} (hh : h≠0) :
    ∃ A : E →L[ℝ] E, IsSelfAdjoint A ∧ ‖A-Q‖≤(K : ℝ) ∧
      A d=h⁻¹ • (G (x+h • d)-G x) := by
  obtain ⟨A,hA,hbound,himage⟩ := exists_selfAdjoint_secant_of_lipschitz_error G Q hQ hG x (h • d)
  refine ⟨A,hA,hbound,?_⟩
  have he := congrArg (fun w => h⁻¹ • w) himage
  rw [map_smul,smul_smul,inv_mul_cancel₀ hh,one_smul] at he
  exact he

end
end krylov.Nonlinear
