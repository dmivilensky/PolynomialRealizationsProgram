import krylov.Methods.HomogeneousSolve
import krylov.Methods.VirtualCoordinates

/-!
Article: main_krylov, lem:U(c,d), genuine virtual-launch coefficient scaling.
Use: propagate source degree-zero coefficients through actual finite virtual
corrections and extrapolated observed gradients before executing XRFC trials.
Source: the proved actual inverse-coefficient homogeneity and physical finite-sum covariance.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual virtual correction, extrapolated gradient and subsequent direction all scale with their true observed vectors.
Use: full-memory XRFC homogeneity is derived from real coefficient solves rather than imposed on its trajectory.
Article: main_krylov, lem:U(c,d), homogeneous virtual launches.
Proof: the real latest model scales quadratically, so its actual model
coefficients stay fixed. Both physical combinations scale and the true
conjugacy direction has the already proved degree-one covariance. -/
theorem virtualBlock_scalar {p : ℕ} (S Y : Fin p → E) (g : E) (c : ℝ) (hc : c≠0) :
    let w := modelCoefficients S (pairModel S Y) g
    let wc := modelCoefficients (fun i => c • S i) (pairModel (fun i => c • S i) (fun i => c • Y i)) (c • g)
    combine (fun i => c • S i) wc=c • combine S w ∧
      c • g+combine (fun i => c • Y i) wc=c • (g+combine Y w) ∧
      conjugacyDirection (fun i => c • S i) (fun i => c • Y i)
        (c • g+combine (fun i => c • Y i) wc)=c • conjugacyDirection S Y (g+combine Y w) := by
  -- The true computed coefficient vector, not just the correction direction, stays fixed.
  simp only [pairModel_scalar,modelCoefficients_scalar S (pairModel S Y) g c hc,combine_scalar]
  rw [← smul_add,conjugacyDirection_scalar _ _ _ c hc]
  exact ⟨trivial,rfl,rfl⟩

end
end krylov.Methods
