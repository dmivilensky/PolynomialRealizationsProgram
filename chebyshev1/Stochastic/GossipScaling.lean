import chebyshev1.Stochastic.GossipRun
import chebyshev1.Jacobi.Basic

/-! Rescaling every sampled Hessian and inversely rescaling the stepsizes leaves
the actual trajectory unchanged.  In particular, unrescaled active graph weights
on the scaled spectral interval give the same sample path as normalized dropout. -/
namespace chebyshev1
noncomputable section
open scoped BigOperators

namespace SpectralInterval

/-- Positive scaling of both physical spectral bounds. -/
def scale (I : SpectralInterval) (c : ℝ) (hc : 0<c) : SpectralInterval where
  mu := c*I.mu
  L := c*I.L
  mu_pos := mul_pos hc I.mu_pos
  mu_lt_L := mul_lt_mul_of_pos_left I.mu_lt_L hc

@[simp] theorem scale_mu (I : SpectralInterval) (c : ℝ) (hc : 0<c) :
    (I.scale c hc).mu=c*I.mu := rfl

@[simp] theorem scale_L (I : SpectralInterval) (c : ℝ) (hc : 0<c) :
    (I.scale c hc).L=c*I.L := rfl

@[simp] theorem scale_delta (I : SpectralInterval) (c : ℝ) (hc : 0<c) :
    (I.scale c hc).delta=c*I.delta := by simp only [delta,scale_mu,scale_L]; ring

@[simp] theorem scale_eta (I : SpectralInterval) (c : ℝ) (hc : 0<c) :
    (I.scale c hc).eta=I.eta := by
  unfold eta
  rw [scale_delta,scale_L,scale_mu]
  field_simp [hc.ne',I.delta_pos.ne']

@[simp] theorem scale_den (I : SpectralInterval) (c : ℝ) (hc : 0<c) (n : ℕ) :
    (I.scale c hc).den n=I.den n := by simp only [den,scale_eta]

@[simp] theorem scale_epsilon (I : SpectralInterval) (c : ℝ) (hc : 0<c) (n : ℕ) :
    (I.scale c hc).epsilon n=I.epsilon n := by simp only [epsilon,scale_den]

@[simp] theorem scale_z (I : SpectralInterval) (c : ℝ) (hc : 0<c) (lam : ℝ) :
    (I.scale c hc).z (c*lam)=I.z lam := by
  unfold z
  rw [scale_delta,scale_L,scale_mu]
  field_simp [hc.ne',I.delta_pos.ne']

theorem scale_residual_eval (I : SpectralInterval) (c : ℝ) (hc : 0<c) (n : ℕ) (lam : ℝ) :
    ((I.scale c hc).residual n).eval (c*lam)=(I.residual n).eval lam := by
  simp only [residual_eval,scale_z,scale_den]

end SpectralInterval

namespace TwoTerm

/-- The inverse stepsize scaling accompanying H_s ↦ c H_s. -/
def rescaleCurvature (S : TwoTerm) (c : ℝ) : TwoTerm where
  a := S.a
  b := S.b
  gamma := fun s => S.gamma s/c

/-- Pathwise identity of the actual finite recurrence, not just its terminal polynomial. -/
theorem variableError_rescaleCurvature (S : TwoTerm) (c : ℝ) (hc : c≠0)
    {d : Type*} [Fintype d] [DecidableEq d]
    (H : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    (S.rescaleCurvature c).variableError (fun s => c • H s) e0 n =
      S.variableError H e0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    simp only [variableError,rescaleCurvature,Matrix.smul_mulVec,smul_smul,div_mul_cancel₀ _ hc]
  | more n ih0 ih1 =>
    simp only [variableError]
    rw [ih0,ih1]
    simp only [rescaleCurvature,Matrix.smul_mulVec,smul_smul,
      div_mul_cancel₀ _ hc]

/-- The deterministic nominal run obeys the identical scaling law. -/
theorem quadraticError_rescaleCurvature (S : TwoTerm) (c : ℝ) (hc : c≠0)
    {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    (S.rescaleCurvature c).quadraticError (c • H) e0 n=S.quadraticError H e0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    simp only [quadraticError,rescaleCurvature,Matrix.smul_mulVec,smul_smul,div_mul_cancel₀ _ hc]
  | more n ih0 ih1 =>
    simp only [quadraticError]
    rw [ih0,ih1]
    simp only [rescaleCurvature,Matrix.smul_mulVec,smul_smul,div_mul_cancel₀ _ hc]

end TwoTerm

namespace JacobiData

@[simp] theorem den_scale (J : JacobiData) (I : SpectralInterval) (c : ℝ) (hc : 0<c) (n : ℕ) :
    J.den (I.scale c hc) n=J.den I n := by simp only [den,SpectralInterval.scale_eta]

/-- Scaling the spectral interval changes exactly the gradient coefficient by 1/c. -/
theorem method_scale (J : JacobiData) (I : SpectralInterval) (c : ℝ) (hc : 0<c) :
    J.method (I.scale c hc)=(J.method I).rescaleCurvature c := by
  unfold method TwoTerm.rescaleCurvature
  simp only [den_scale,SpectralInterval.scale_eta,SpectralInterval.scale_delta]
  congr 1
  funext s
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end JacobiData

namespace Stochastic
variable {d e Ω : Type*} [Fintype d] [DecidableEq d] [Fintype e]

/-- Sampled edge weights with no division by their activation probability. -/
def rawDropoutLaplacian (A : e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (ω : Ω) :
    Matrix d d ℝ :=
  edgeLaplacian (fun i => (A i).indicator (1 : Ω → ℝ) ω*w i) b

omit [Fintype d] [DecidableEq d] in
theorem rawDropoutLaplacian_eq (p : ℝ) (hp : p<1) (A : e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (ω : Ω) :
    rawDropoutLaplacian A w b ω=(1-p) • dropoutLaplacian p A w b ω := by
  unfold rawDropoutLaplacian dropoutLaplacian edgeLaplacian
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  field_simp [(sub_pos.mpr hp).ne']

end Stochastic

namespace TwoTerm
variable {d e Ω : Type*} [Fintype d] [DecidableEq d] [Fintype e]

def unscaledGossipError (S : TwoTerm) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ d :=
  WithLp.toLp 2 (S.variableError (fun s => Stochastic.rawDropoutLaplacian (A s) w b ω)
    (WithLp.ofLp e0) n)

theorem unscaledGossipError_rescale (S : TwoTerm) (p : ℝ) (hp : p<1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (n : ℕ) (ω : Ω) :
    (S.rescaleCurvature (1-p)).unscaledGossipError A w b e0 n ω =
      S.gossipError p A w b e0 n ω := by
  unfold unscaledGossipError gossipError
  simp only [Stochastic.rawDropoutLaplacian_eq p hp]
  exact congrArg (WithLp.toLp 2) (S.variableError_rescaleCurvature (1-p) (sub_pos.mpr hp).ne' _ _ n)

end TwoTerm

namespace JacobiData
variable {d e Ω : Type*} [Fintype d] [DecidableEq d] [Fintype e]

/-- Literal unscaled edge weights on (1-p)[mu,L] give the identical actual
trajectory to the normalized dropout method on [mu,L], sample by sample. -/
theorem unscaledGossipError_scale (J : JacobiData) (I : SpectralInterval)
    (p : ℝ) (hp : p<1) (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) :
    (J.method (I.scale (1-p) (sub_pos.mpr hp))).unscaledGossipError A w b e0 n ω =
      (J.method I).gossipError p A w b e0 n ω := by
  rw [J.method_scale]
  exact (J.method I).unscaledGossipError_rescale p hp A w b e0 n ω

/-- The nominal error is scaled as well, so the exact finite variance and its
remainder transport with the same Gamma, rather than merely the same raw output. -/
theorem unscaledGossipDiscrepancy_scale (J : JacobiData) (I : SpectralInterval)
    (p : ℝ) (hp : p<1) (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) :
    (J.method (I.scale (1-p) (sub_pos.mpr hp))).unscaledGossipError A w b e0 n ω -
      WithLp.toLp 2 ((J.method (I.scale (1-p) (sub_pos.mpr hp))).quadraticError
        ((1-p) • Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n) =
    (J.method I).gossipError p A w b e0 n ω -
      WithLp.toLp 2 ((J.method I).quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n) := by
  rw [J.unscaledGossipError_scale I p hp,J.method_scale]
  rw [(J.method I).quadraticError_rescaleCurvature (1-p) (sub_pos.mpr hp).ne']

end JacobiData
end
end chebyshev1
