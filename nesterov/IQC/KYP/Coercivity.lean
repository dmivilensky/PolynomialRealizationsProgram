import nesterov.IQC.KYP.Bounds
import nesterov.IQC.Execution
import nesterov.IQC.MiddleRadius

/-!
Positivity of the constructed finite-state storage follows from its actual
square-summable discounted tail and strict dissipation. All comparison
constants are fixed by the method, exponent and finite certificate.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators Topology
open Filter
open polyak.General.IQC polyak.Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The complete finite window after discounting is exactly a finite sum of
shifted latent energies, with fixed positive coefficients. -/
theorem discounted_window_energy (N : ℕ) (t : ℝ) (w : ℕ→E) (k : ℕ) :
    Real.exp (-2*(k:ℝ)*t)*windowEnergy N w k=
      ∑ j : Fin N,Real.exp (2*j.val*t)*‖discountedPosition w t (k+j.val)‖^2 := by
  rw [windowEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_discountedPosition_sq]
  unfold polyak.Growth.discountedEnergy
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  push_cast
  ring

/-- Every finite discounted state window has summable energy. -/
theorem summable_discounted_window (N : ℕ) (t : ℝ) {w : ℕ→E}
    (hw : SquareSummable (discountedPosition w t)) :
    Summable (fun k : ℕ=>Real.exp (-2*(k:ℝ)*t)*windowEnergy N w k) := by
  simp_rw [discounted_window_energy]
  apply summable_sum
  intro j _
  exact ((summable_nat_add_iff j.val).mpr hw).mul_left _

end
end nesterov.IQC.KYP

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators Topology
open Filter
open nesterov.IQC nesterov.IQC.KYP polyak.General.IQC polyak.Energy
variable (A : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The constructed storage has a vanishing discounted tail. -/
theorem lyapunov_discounted_limit {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M) (W : Bilinear (Fin (A.memory+M)→ℝ))
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : SquareSummable (discountedPosition w t)) :
    Tendsto (fun k : ℕ=>(Real.exp (2*t)^k)⁻¹*A.lyapunov cert W ψ w k) atTop (𝓝 0) := by
  have hs:=summable_discounted_window (A.memory+M) t hw
  have ht : Tendsto (fun k : ℕ=>A.lyapunovUpper cert W*
      (Real.exp (-2*(k:ℝ)*t)*windowEnergy (A.memory+M) w k)) atTop (𝓝 0) := by
    have hh : Tendsto (fun k : ℕ=>Real.exp (-2*(k:ℝ)*t)*windowEnergy (A.memory+M) w k)
        atTop (𝓝 0) := by simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
    simpa only [mul_zero] using hh.const_mul (A.lyapunovUpper cert W)
  have hn : ∀ k : ℕ,‖(Real.exp (2*t)^k)⁻¹*A.lyapunov cert W ψ w k‖≤
      A.lyapunovUpper cert W*(Real.exp (-2*(k:ℝ)*t)*windowEnergy (A.memory+M) w k) := by
    intro k
    have he : (Real.exp (2*t)^k)⁻¹=Real.exp (-2*(k:ℝ)*t) := by
      rw [←Real.exp_nat_mul,←Real.exp_neg]
      congr 1
      ring
    rw [he,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hh:=mul_le_mul_of_nonneg_left (A.lyapunov_abs_bound cert hM W hψ w k)
      (Real.exp_pos (-2*(k:ℝ)*t)).le
    exact hh.trans_eq (by ring)
  exact squeeze_zero_norm hn ht

/-- The actual Lyapunov expression is quantitatively positive on every
trajectory; positivity is proved, not assumed of the storage matrix. -/
theorem lyapunov_comparison {μ L t : ℝ} {M : ℕ} (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius A μ L<Real.exp t)
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (η : ℝ) (hη : 0<η)
    (hW : ∀ (x : Fin (A.memory+M)→ℝ) (d : ℝ),
      W (registerStep x d) (registerStep x d)-W x x+
        instantaneous (ofKernel (A.polynomialKernel cert)) x d≤
          -η*((∑ j,‖x j‖^2)+‖d‖^2))
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    ((η*Real.exp (-2*(A.memory+M:ℕ)*|t|))/Real.exp (2*t))*windowEnergy (A.memory+M) w k≤
      A.lyapunov cert W ψ w k ∧
    A.lyapunov cert W ψ w k≤A.lyapunovUpper cert W*windowEnergy (A.memory+M) w k := by
  have he:=A.latent_execution_bound hμL
    (fun z hz=>(normalized_root_norm_le A hμ hμL hz).trans_lt hr) hψ cert w hw
  have hs : SquareSummable (discountedPosition w t) := by
    change SquareSummable (fun k : ℕ=>Real.exp (-((k:ℝ)*t)) • w k)
    simpa only [neg_mul] using he.1
  have hlim:=A.lyapunov_discounted_limit cert hM W hψ w hs
  have hstep:=A.lyapunov_dissipation cert hM W η hη.le hW hψ w hw
  have hb (n : ℕ) : 0≤windowEnergy (A.memory+M) w n:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hη' : 0≤η*Real.exp (-2*(A.memory+M:ℕ)*|t|):=mul_nonneg hη.le (Real.exp_pos _).le
  have hp:=storage_coercive_of_discounted_limit (Real.exp_pos (2*t)) hη' hb hstep hlim
  exact ⟨hp.2 k,(le_abs_self _).trans (A.lyapunov_abs_bound cert hM W hψ w k)⟩

end
end nesterov.StationaryMethod
