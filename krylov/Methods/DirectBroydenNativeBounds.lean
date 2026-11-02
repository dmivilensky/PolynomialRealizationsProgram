import krylov.Methods.DirectBroydenFinite
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), derived native perturbation domains.
Use: the actual chronological native models have true bounded operators
and inverse old curvatures for arbitrary original convex schedules.
Source: exact finite-array dictionary, positive reference pair limits and
the proved compact native parameter bounds.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open Set Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual finite native model and its actual next inverse old
curvature are bounded near genuine positive reference pair limits,
uniformly over arbitrary original convex interpolation schedules.
Use: derive the native bounds used in the full source comparison from
primitive pair limits rather than assuming a bounded-model hypothesis.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the exact newest-first array chart preserves the actual model and
every interpolation coordinate. Its genuine finite parameter cube gives
the actual two bounds along convergent observed data. -/
theorem directBroydenNative_bounds (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (k : ℕ) (D0 : ℕ → E × E) (hpair : ∀ i<k,0 < inner ℝ (D0 i).1 (D0 i).2)
    (s0 : E) (hs0 : s0≠0) (l : Filter α) (phi : α → ℕ → ℝ)
    (D : α → ℕ → E × E) (s : α → E)
    (hphi : ∀ᶠ z in l,∀ i<k,0≤phi z i ∧ phi z i≤1)
    (hD : ∀ i<k,Tendsto (fun z => D z i) l (𝓝 (D0 i))) (hs : Tendsto s l (𝓝 s0)) :
    (fun z => directBroydenNative B0 (phi z) (D z) k) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => (inner ℝ (s z) (directBroydenNative B0 (phi z) (D z) k (s z)))⁻¹)
      =O[l] (fun _ => (1 : ℝ)) := by
  have h := directBroydenFiniteModel_uniform_bounds B0 hB0 hpos
    (fun i : Fin k => D0 (k-1-i.val)) (fun i => hpair _ (by omega)) s0 hs0 l
    (fun z (i : Fin k) => phi z i.val) (fun z (i : Fin k) => D z (k-1-i.val)) s
    (hphi.mono (fun _ hz i => hz i.val i.isLt))
    (tendsto_pi_nhds.mpr (fun i => hD _ (by omega))) hs
  simpa only [directBroydenNative_finite] using h

/-- Actual native direct models remain symmetric and strictly positive
whenever their true finite observed curvatures and actual interpolation
coordinates are positive and nonnegative, respectively.
Use: derive actual perturbation denominator domains locally from true
reference pair limits; no global off-prefix schedule condition is imposed.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the exact finite chart agrees with every original executed update;
zero extension preserves all genuine finite nonnegative parameters. Apply
the already proved positive native chronological recursion. -/
theorem directBroydenNative_positive (B0 : E →L[ℝ] E)
    (hB0 : B0.toLinearMap.IsSymmetric) (hpos : ∀ w : E,w≠0 → 0 < inner ℝ w (B0 w))
    (phi : ℕ → ℝ) (D : ℕ → E × E) (k : ℕ)
    (hphi : ∀ i<k,0≤phi i) (hpair : ∀ i<k,0 < inner ℝ (D i).1 (D i).2) :
    (directBroydenNative B0 phi D k).toLinearMap.IsSymmetric ∧
      ∀ w : E,w≠0 → 0 < inner ℝ w (directBroydenNative B0 phi D k w) := by
  rw [directBroydenNative_finite]
  apply directBroydenOperatorModel_positive B0 hB0 hpos
  · intro i
    unfold directBroydenFiniteSchedule
    split_ifs with hi
    · exact hphi i hi
    · exact le_refl 0
  · exact List.forall_mem_ofFn_iff.mpr (fun i => hpair _ (by omega))

end
end krylov.Methods
