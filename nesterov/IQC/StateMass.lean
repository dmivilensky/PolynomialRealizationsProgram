import nesterov.IQC.Execution
import nesterov.IQC.EnergyRate
import nesterov.IQC.MiddleRadius

/-!
The uniform latent ℓ² estimate controls every complete state window. Restarting
then gives the strict one-exponent rate bound, with the exact stability
threshold r_c of the uncancelled middle-curvature polynomial.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC

/-- Complete-state window loss when passing from latent energy to state energy. -/
def windowMass (M : StationaryMethod) (t : ℝ) : ℝ:=
  ∑ j : Fin M.memory,Real.exp (2*j.val*t)

theorem windowMass_nonneg (M : StationaryMethod) (t : ℝ) : 0≤windowMass M t:=
  Finset.sum_nonneg (fun _ _=>(Real.exp_pos _).le)

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Discounted complete-state energy is a finite sum of shifted latent energies. -/
theorem discountedState_window (M : StationaryMethod) (t : ℝ) (w : ℕ→E) (k : ℕ) :
    Real.exp (-2*(k:ℝ)*t)*(M.stateNorm w k)^2=
      ∑ j : Fin M.memory,Real.exp (2*j.val*t)*
        ‖Real.exp (-((k+j.val:ℕ):ℝ)*t) • w (k+j.val)‖^2 := by
  rw [M.stateNorm_sq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,←Real.exp_nat_mul]
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  push_cast
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A finite shifted energy sum is bounded by the full nonnegative energy. -/
theorem shifted_energy_sum_le {x : ℕ→E} (hx : SquareSummable x) (j N : ℕ) :
    (∑ k∈Finset.range (N+1),‖x (k+j)‖^2)≤∑' k,‖x k‖^2 := by
  have hs : Summable (fun k : ℕ=>‖x (k+j)‖^2):=
    (summable_nat_add_iff j).mpr hx
  have hp:=hs.sum_le_tsum (Finset.range (N+1)) (fun k _=>sq_nonneg ‖x (k+j)‖)
  have ht : (∑' k,‖x (k+j)‖^2)≤∑' k,‖x k‖^2 := by
    have he:=hx.sum_add_tsum_nat_add j
    have hn : 0≤∑ k∈Finset.range j,‖x k‖^2:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    linarith
  exact hp.trans ht

omit [CompleteSpace E] in
/-- The finite-window transfer uses the entire memory, including hidden modes. -/
theorem stateMass_le_latent (M : StationaryMethod) (t : ℝ) (w : ℕ→E)
    (hw : SquareSummable (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • w k)) (N : ℕ) :
    (∑ k∈Finset.range (N+1),Real.exp (-2*(k:ℝ)*t)*(M.stateNorm w k)^2)≤
      windowMass M t*(sequenceNorm (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • w k))^2 := by
  simp_rw [discountedState_window]
  rw [Finset.sum_comm,windowMass,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [←Finset.mul_sum,sequenceNorm_sq]
  exact mul_le_mul_of_nonneg_left (shifted_energy_sum_le hw j.val N) (Real.exp_pos _).le

end Hilbert

/-- A strict certificate supplies a single complete-state energy constant for
all actual Hilbert executions, before any asymptotic limit is taken. -/
theorem certificate_uniformStateMass {M : StationaryMethod} {μ L t : ℝ}
    (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) :
    UniformStateMassBound M μ L t (windowMass M t*(M.executionGain cert)^2) := by
  intro r N
  have he:=M.latent_execution_bound hμL hstable r.admissible.normalize cert r.w
    (r.trajectory.normalized M r.admissible.differentiable)
  have hn:=sq_le_sq₀ (sequenceNorm_nonneg _)
    (mul_nonneg (M.executionGain_nonneg cert) (M.stateNorm_nonneg r.w 0)) |>.mpr he.2
  have hm:=mul_le_mul_of_nonneg_left hn (windowMass_nonneg M t)
  have hs:=stateMass_le_latent M t r.w he.1 N
  exact hs.trans (by simpa only [discountedState,Rates.HilbertRun.stateNorm,mul_pow,mul_assoc] using hm)

/-- Theorem A(c), first assertion: one strict certificate above r_c suffices.
No coprimality, original stability, or second exponent is assumed. -/
theorem one_exponent {M : StationaryMethod} {μ L t : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius M μ L<Real.exp t)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) :
    Rates.rate M μ L<Real.exp t := by
  apply rate_lt_exp_of_uniformStateMassBound hμ hμL
    (mul_nonneg (windowMass_nonneg M t) (sq_nonneg (M.executionGain cert)))
  exact certificate_uniformStateMass hμL
    (fun z hz=>(normalized_root_norm_le M hμ hμL hz).trans_lt hr) cert

end
end nesterov.IQC
