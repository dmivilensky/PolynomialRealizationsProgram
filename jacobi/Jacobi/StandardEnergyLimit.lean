import jacobi.Jacobi.StandardBounds
import jacobi.Analysis.BoundedMesh

/-!
The genuine standard finite Green energy converges to its one-sided
kernel integral. The proved global entry bound dominates every mesh,
including the singular small-index corner. The endpoint is therefore
handled by the same dominated convergence argument as the interior.
Use: StandardJacobi evaluates this integral and StandardDescent uses
the resulting actual finite initial energy in the flow's Taylor estimate.
Article: jacobi, Theorem 5.4.
Article role: dominated convergence and exact power or logarithmic evaluation of the one-sided
energy.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory jacobi.Analysis chebyshev1.Analysis chebyshev2
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized finite diagonal-square sum is exactly the actual
standard Jacobi energy, rather than a model quadrature of its limit.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_mesh_identity {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    (∑ j∈Finset.range N,(standardGreenTail a b N j j/(N:ℝ))^2)/(N:ℝ)=
      (standardChain a b ha hb N).energy/(N:ℝ)^3 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (standardGreenTail a b N j j/(N:ℝ))^2) N]
  have he : (∑ j:Fin N,(standardGreenTail a b N j j/(N:ℝ))^2)=
      ∑ j:Fin N,((standardChain a b ha hb N).green j j/(N:ℝ))^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [standardGreenTail_entry_of_le ha hb j j le_rfl]
  rw [he]
  simp only [div_pow,← Finset.sum_div,div_div,Jacobi.energy]
  congr 1

/-- Full actual standard-chain energy convergence to the one-sided
Green-diagonal integral, with all finite and boundary estimates proved.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_integral_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun N : ℕ => (standardChain a b (by linarith : -1<a) hb N).energy/(N:ℝ)^3)
      atTop (𝓝 (∫ t in (0:ℝ)..1,(standardLimitKernel a t t)^2)) := by
  have ha' : -1<a := by linarith
  obtain ⟨K,hK,hbound⟩ := standardGreenTail_normalized_bound ha hb
  have hbnd : ∀ᶠ N : ℕ in atTop,∀ j,
      |(standardGreenTail a b N j j/(N:ℝ))^2|≤K^2 := by
    exact Eventually.of_forall (fun N j => by
      rw [abs_of_nonneg (sq_nonneg _),← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound N j j) 2)
  have hp : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun N : ℕ => (standardGreenTail a b N (Nat.floor ((N:ℝ)*t))
        (Nat.floor ((N:ℝ)*t))/(N:ℝ))^2) atTop (𝓝 ((standardLimitKernel a t t)^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hm := floor_mesh_limit (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop)
      (tendsto_const_nhds (x := t)) (Eventually.of_forall (fun _ => ht.1.le))
    exact (standardGreenTail_mesh_limit ha' hb id (fun N => Nat.floor ((N:ℝ)*t))
      (fun N => Nat.floor ((N:ℝ)*t)) ⟨ht.1,ht.2.le⟩ ⟨ht.1,ht.2.le⟩ tendsto_id hm hm).pow 2
  have h := bounded_mesh_limit id (fun N j => (standardGreenTail a b N j j/(N:ℝ))^2)
    (fun t => (standardLimitKernel a t t)^2) tendsto_id hbnd hp
  simpa only [id_eq,standard_energy_mesh_identity ha' hb] using h

end
end jacobi.Jacobi
