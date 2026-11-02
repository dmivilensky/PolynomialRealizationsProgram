import chebyshev1.Chebyshev.Normalization
import Mathlib.LinearAlgebra.Prod

/-!
Article: bezout, Equations `eq:experiment-network` and `eq:experiment-channel`.
Use: two coupled networks have the stated antisymmetric invariant subspace,
channel projector and active eigenvalues, with an interval-independent chart.
Proof: explicit block action, projection identities and scalar normalization.
-/

namespace bezout.Models.Network
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The inter-network disagreement channel, in its literal two-block form. -/
def projector (x : E×E) : E×E := ((1/2:ℝ) • (x.1-x.2), (1/2:ℝ) • (x.2-x.1))

/-- Antisymmetric disagreement embedded into the two physical networks. -/
def antisymmetric (z : E) : E×E := (z,-z)

/-- The normalized Hessian of two corresponding-vertex coupled networks. -/
def hessian (Lc : E →ₗ[ℝ] E) (a : ℝ) (x : E×E) : E×E :=
  ((4+2*a)⁻¹ • (Lc x.1+a • (x.1-x.2)),
   (4+2*a)⁻¹ • (Lc x.2+a • (x.2-x.1)))

/-- The channel is an actual projection onto the antisymmetric subspace. -/
theorem projector_idempotent (x : E×E) : projector (projector x)=projector x := by
  ext <;> simp only [projector] <;> module

/-- The shared channel acts as the identity on all physical disagreement states. -/
theorem projector_antisymmetric (z : E) : projector (antisymmetric z)=antisymmetric z := by
  ext <;> simp only [projector, antisymmetric] <;> module

/-- Every projected state is antisymmetric, and every antisymmetric state is projected. -/
theorem projector_range (x : E×E) :
    (∃ z, x=antisymmetric z) ↔ projector x=x := by
  constructor
  · rintro ⟨z,rfl⟩
    exact projector_antisymmetric z
  · intro hx
    refine ⟨x.1, ?_⟩
    have he := congrArg Prod.snd hx
    change (1/2:ℝ) • (x.2-x.1)=x.2 at he
    have hs : x.2= -x.1 := by
      calc
        x.2 = 2 • ((1/2:ℝ) • (x.2-x.1)) - x.2 := by rw [he]; module
        _ = -x.1 := by module
    exact Prod.ext rfl hs

/-- Restriction of the physical Hessian is exactly (Lc+2aI)/(4+2a). -/
theorem hessian_antisymmetric (Lc : E →ₗ[ℝ] E) (a : ℝ) (z : E) :
    hessian Lc a (antisymmetric z)=
      antisymmetric ((4+2*a)⁻¹ • (Lc z+(2*a) • z)) := by
  ext <;> simp only [hessian, antisymmetric, map_neg] <;> module

/-- The channel commutes with the reference Hessian on all states. -/
theorem projector_commutes (Lc : E →ₗ[ℝ] E) (a : ℝ) (x : E×E) :
    projector (hessian Lc a x)=hessian Lc a (projector x) := by
  ext <;> simp only [projector, hessian, map_smul, map_sub] <;> module

/-- Each cycle eigenmode lifts to the claimed physical active eigenvalue. -/
theorem eigenmode (Lc : E →ₗ[ℝ] E) (a ell : ℝ) (z : E) (hz : Lc z=ell • z) :
    hessian Lc a (antisymmetric z)=((ell+2*a)/(4+2*a)) • antisymmetric z := by
  rw [hessian_antisymmetric, hz]
  ext <;> simp only [antisymmetric, Prod.smul_fst, Prod.smul_snd] <;> module

/-- The coupling chosen in the article is strictly positive for every condition number above one. -/
theorem coupling_pos (κ : ℝ) (hκ : 1<κ) : 0<2/(κ-1) := div_pos (by norm_num) (by linarith)

/-- The active lower and upper cycle endpoints give exactly 1/kappa and one. -/
theorem active_endpoints (κ : ℝ) (hκ : 1<κ) :
    (0+2*(2/(κ-1)))/(4+2*(2/(κ-1)))=1/κ ∧
    (4+2*(2/(κ-1)))/(4+2*(2/(κ-1)))=1 := by
  have hk0 : κ≠0 := by linarith
  have hkm : κ-1≠0 := by linarith
  have hd : 4+2*(2/(κ-1))≠0 := ne_of_gt (by have := coupling_pos κ hκ; linarith)
  constructor
  · field_simp [hk0, hkm, hd]
    ring_nf
    exact mul_inv_cancel₀ hk0
  · exact div_self hd

/-- The Chebyshev coordinate of every active cycle eigenvalue is independent of kappa. -/
theorem chart_cancellation (κ ell : ℝ) (hκ : 1<κ) :
    let I : chebyshev1.SpectralInterval :=
      ⟨1/κ,1,one_div_pos.mpr (by linarith), (div_lt_one (by linarith : 0<κ)).mpr hκ⟩
    I.z ((ell+2*(2/(κ-1)))/(4+2*(2/(κ-1))))=1-ell/2 := by
  have hk0 : κ≠0 := by linarith
  have hkm : κ-1≠0 := by linarith
  have hd : 4+2*(2/(κ-1))≠0 := ne_of_gt (by have := coupling_pos κ hκ; linarith)
  have hden : 4+2*(2/(κ-1))=4*κ/(κ-1) := by field_simp; ring
  dsimp [chebyshev1.SpectralInterval.z, chebyshev1.SpectralInterval.delta]
  rw [hden]
  field_simp [hk0, hkm]
  ring

/-- The varying-channel oracle changes exactly the corresponding-vertex conductance. -/
theorem channel_block_action (Lc : E →ₗ[ℝ] E) (a t : ℝ) (x : E×E) :
    hessian Lc a x+t • projector x=
      ((4+2*a)⁻¹ • Lc x.1+(a/(4+2*a)+t/2) • (x.1-x.2),
       (4+2*a)⁻¹ • Lc x.2+(a/(4+2*a)+t/2) • (x.2-x.1)) := by
  ext <;> dsimp [hessian, projector] <;> simp only [div_eq_mul_inv] <;> module

/-- Every bounded signed channel perturbation below the lower endpoint retains positive edges. -/
theorem channel_weight_pos (κ δ ξ : ℝ) (hκ : 1<κ) (hδ : |δ|<1/κ) (hξ : |ξ|≤1) :
    0<(2/(κ-1))/(4+2*(2/(κ-1)))+δ*ξ/2 := by
  have he := (active_endpoints κ hκ).1
  have hbase : (2/(κ-1))/(4+2*(2/(κ-1)))=(1/κ)/2 := by
    have hh : (0+2*(2/(κ-1)))/(4+2*(2/(κ-1)))=
        2*((2/(κ-1))/(4+2*(2/(κ-1)))) := by ring
    rw [hh] at he
    linarith
  rw [hbase]
  have hprod : |δ*ξ|<1/κ :=
    (abs_mul δ ξ).symm ▸ (mul_le_mul_of_nonneg_left hξ (abs_nonneg δ)).trans_lt (by simpa using hδ)
  have hl := (abs_lt.mp hprod).1
  linarith

end
end bezout.Models.Network
