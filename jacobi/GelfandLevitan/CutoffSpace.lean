import jacobi.Reference.HalfSpace

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Each physical interval is the genuine closed subspace of original
half-interval L2 vectors vanishing beyond its actual endpoint. The
community measurable restriction and orthogonal projection supply
the exact source P_t. Its two endpoint values, symmetry, idempotence
and norm bound are proved for these original spaces.
Use: its actual measurable restriction defines precisely the zero-extended source L2(0,t) subspace.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine portion of the original unit interval lying beyond a prescribed physical endpoint.
Use: its actual measurable restriction defines precisely the zero-extended source L2(0,t) subspace.
Article: jacobi, Proposition C.2.
-/
def outsideBefore (t : ℝ) : Set Interval := {s | t<(s:ℝ)}

/-- Every actual physical cutoff tail is measurable in the original Lebesgue subtype measure.
Use: the genuine kernel of its continuous restriction is characterized by the exact source almost-everywhere support condition.
Article: jacobi, Proposition C.2.
Proof: the actual cutoff tail is the preimage of an open real half-line under the continuous original spatial coordinate. -/
theorem outsideBefore_measurable (t : ℝ) : MeasurableSet (outsideBefore t) :=
  (isOpen_lt continuous_const continuous_subtype_val).measurableSet

/-- The genuine continuous restriction of original half-domain L2 vectors to the portion beyond the actual endpoint t.
Use: its actual closed kernel is the physical source L2(0,t) domain used by the original GL cutoff equation.
Article: jacobi, Proposition C.2.
-/
def cutoffRestriction (t : ℝ) : halfSubspace →L[ℝ]
    Lp ℝ 2 ((volume : Measure Interval).restrict (outsideBefore t)) :=
  (LpToLpRestrictCLM Interval ℝ ℝ volume 2 (outsideBefore t)).comp halfSubspace.subtypeL

/-- The genuine closed original Hilbert domain of inputs supported before the physical endpoint t.
Use: the actual source orthogonal projection P_t and compressed GL operators act on this original interval subspace.
Article: jacobi, Proposition C.2.
-/
def cutoffSubspace (t : ℝ) : Submodule ℝ halfSubspace := (cutoffRestriction t).ker

/-- Membership in the genuine cutoff Hilbert domain is precisely vanishing almost everywhere beyond the original physical endpoint.
Use: identifies the actual source P_t with the original interval cutoff and applies the proved uniform coercivity to every true interval input.
Article: jacobi, Proposition C.2.
Proof: the community Lp restriction representative is the actual
original function almost everywhere for the restricted measure. Its
zero class is therefore exactly the original measurable tail-vanishing
condition, with no approximation of the source interval. -/
theorem mem_cutoffSubspace_iff (t : ℝ) (v : halfSubspace) :
    v∈cutoffSubspace t ↔ ∀ᵐ s:Interval,t<(s:ℝ) → (v:Space) s=0 := by
  -- Restriction and its null class refer to the same actual original L2 representative.
  change cutoffRestriction t v=0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have he : cutoffRestriction t v=ᵐ[(volume : Measure Interval).restrict (outsideBefore t)] (v:Space) :=
    LpToLpRestrictCLM_coeFn ℝ (outsideBefore t) (v:Space)
  constructor
  · intro hz
    have hh := he.symm.trans hz
    simpa only [outsideBefore,Set.mem_ofPred_eq,Pi.zero_apply] using
      (ae_restrict_iff' (outsideBefore_measurable t)).mp hh
  · intro hv
    exact he.trans ((ae_restrict_iff' (outsideBefore_measurable t)).mpr hv)

/-- The actual original physical cutoff domain is closed in the genuine half-interval Hilbert space.
Use: its source orthogonal projection exists in the actual complete Hilbert geometry.
Article: jacobi, Proposition C.2.
Proof: it is the genuine kernel of the actual continuous linear restriction map. -/
theorem cutoffSubspace_closed (t : ℝ) : IsClosed (cutoffSubspace t : Set halfSubspace) :=
  (cutoffRestriction t).isClosed_ker

/-- Every actual original cutoff Hilbert domain is complete in its inherited true L2 norm.
Use: the community orthogonal projection applies to each genuine source physical interval.
Article: jacobi, Proposition C.2.
Proof: the original interval domain is a proved closed subspace of the actual complete half-interval Hilbert space. -/
instance cutoffSubspace_complete (t : ℝ) : CompleteSpace (cutoffSubspace t) :=
  (cutoffSubspace_closed t).completeSpace_coe

/-- The genuine source projection onto original L2 inputs supported before the actual physical endpoint.
Use: defines the actual family I+P_t*F*P_t in the original GL construction.
Article: jacobi, Proposition C.2.
-/
def cutoffProjection (t : ℝ) : halfSubspace →L[ℝ] halfSubspace := (cutoffSubspace t).starProjection

/-- The genuine original cutoff projection has operator norm at most one for every physical endpoint.
Use: the actual compressed kernel series has the same uniform summable norm majorant as the original F operator.
Article: jacobi, Proposition C.2.
Proof: use the community orthogonal projection norm theorem on the actual original closed cutoff domain. -/
theorem cutoffProjection_norm_le (t : ℝ) : ‖cutoffProjection t‖≤1 :=
  (cutoffSubspace t).starProjection_norm_le

/-- The actual original cutoff projection is symmetric in the genuine Hilbert inner product.
Use: the compressed original GL form is the kernel form of P_t*v, giving the true uniform source coercivity on every interval.
Article: jacobi, Proposition C.2.
Proof: the community orthogonal projection onto the actual closed cutoff domain is symmetric. -/
theorem cutoffProjection_symmetric (t : ℝ) : (cutoffProjection t).IsSymmetric :=
  (cutoffSubspace t).starProjection_isSymmetric

/-- The actual original cutoff projection is idempotent on every true original Hilbert vector.
Use: the source compressed inverse equation preserves the original interval support.
Article: jacobi, Proposition C.2.
Proof: evaluate the community idempotent orthogonal-projection identity on the actual original vector. -/
theorem cutoffProjection_idempotent (t : ℝ) (v : halfSubspace) :
    cutoffProjection t (cutoffProjection t v)=cutoffProjection t v := by
  have hh := congrArg (fun T:halfSubspace →L[ℝ] halfSubspace => T v)
    (cutoffSubspace t).isIdempotentElem_starProjection
  exact hh

/-- The actual projected original input belongs to the genuine physical cutoff domain.
Use: its source representative is zero almost everywhere beyond t, exactly as required in the original GL integral equation.
Article: jacobi, Proposition C.2.
Proof: the original star projection is the inclusion of its actual orthogonal-projection vector in the genuine closed cutoff subspace. -/
theorem cutoffProjection_mem (t : ℝ) (v : halfSubspace) : cutoffProjection t v∈cutoffSubspace t := by
  change ((cutoffSubspace t).orthogonalProjectionOnto v:halfSubspace)∈cutoffSubspace t
  exact ((cutoffSubspace t).orthogonalProjectionOnto v).property

/-- At the actual midpoint the original cutoff domain is the whole true half-interval Hilbert space.
Use: the source compressed operator at t=1/2 is exactly the already constructed original I+F operator.
Article: jacobi, Proposition C.2.
Proof: every original half-domain vector has precisely the proved actual zero-extension support condition at one half. -/
theorem cutoffSubspace_half : cutoffSubspace (1/2)=⊤ := by
  apply le_antisymm le_top
  intro v _
  exact (mem_cutoffSubspace_iff _ v).mpr (halfSubspace_supported v)

/-- The original zero-length cutoff domain is genuinely zero in the actual original Lebesgue Hilbert space.
Use: fixes the true source endpoint P_0=0 in the GL construction and its continuity argument.
Article: jacobi, Proposition C.2.
Proof: an original input supported before zero vanishes almost
everywhere on the genuine interval interior, which already has full
original measure. Its true full L2 class and half-domain class are zero. -/
theorem cutoffSubspace_zero : cutoffSubspace 0=⊥ := by
  -- Both original interval endpoints are null; the original open interval has the actual full measure.
  apply le_antisymm ?_ bot_le
  intro v hv
  change v=0
  have hz : (v:Space)=0 := Lp.eq_zero_iff_ae_eq_zero.mpr (by
    filter_upwards [(mem_cutoffSubspace_iff 0 v).mp hv,interval_interior_ae] with s hs hsi
    exact hs hsi.1)
  exact Subtype.ext hz

/-- The actual source cutoff projection at zero is the genuine zero operator.
Use: fixes the original zero-interval inverse and zero GL row.
Article: jacobi, Proposition C.2.
Proof: the actual original cutoff subspace at zero is proved to be the zero subspace; use the community projection endpoint identity. -/
theorem cutoffProjection_zero : cutoffProjection 0=0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hh := cutoffProjection_mem 0 v
  rw [cutoffSubspace_zero] at hh
  change cutoffProjection 0 v=0 at hh
  exact hh

/-- The actual original midpoint cutoff projection is the genuine identity operator.
Use: the source compressed family at the midpoint is exactly the original positive operator already proved invertible.
Article: jacobi, Proposition C.2.
Proof: the actual original cutoff subspace at the midpoint is the full genuine half-domain; its community orthogonal projection is the identity. -/
theorem cutoffProjection_half : cutoffProjection (1/2)=ContinuousLinearMap.id ℝ halfSubspace := by
  apply ContinuousLinearMap.ext
  intro v
  change (cutoffSubspace (1/2)).starProjection v=v
  exact (cutoffSubspace (1/2)).starProjection_eq_self_iff.mpr
    ((mem_cutoffSubspace_iff _ v).mpr (halfSubspace_supported v))

end
end jacobi.GelfandLevitan
