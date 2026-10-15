import «2610.05164v2».DualCertificate.CoefficientContinuity
import «2610.05164v2».DualCertificate.StateContinuity
import «2610.05164v2».DualCertificate.Stability
import «2610.05164v2».Residual.SmoothConjugate

/-!
Article: 2610.05164v2, Theorem 3.6.
E.1: strict admissibility of the literal finite cell certificate persists near every positive ground
parameter.
Use: `«2610.05164v2».DualCertificate.Data.admissible_stable` feeds
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` (uniform finite lower bound).
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k,∀ x,F (κ,x)<0`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this bound to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem positive_compact_strict_stability {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : Ioi (0:ℝ) × X → ℝ} (hF : Continuous F) (k : Ioi (0:ℝ))
    (hn : ∀ x,F (k,x)<0) : ∀ᶠ κ in 𝓝 k,∀ x,F (κ,x)<0 := by
  have hlocal : ∀ x∈(univ:Set X),∀ᶠ p : Ioi (0:ℝ) × X in 𝓝 (k,x),F p<0 :=
    fun x _ => hF.continuousAt.eventually (gt_mem_nhds (hn x))
  exact (isCompact_univ.eventually_forall_of_forall_eventually hlocal).mono
    (fun _ h x => h x (mem_univ _))

namespace Data
open «2610.05164v2».Residual
variable (D : «2610.05164v2».DualCertificate.Data)

/--
Defines `StabilityBox` of type `` by `Icc (0:ℝ) 1 × Icc (0:ℝ) 1 × Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev StabilityBox := Icc (0:ℝ) 1 × Icc (0:ℝ) 1 × Icc (0:ℝ) 1
/--
Defines `FaceIndex` of type `` by `Σ side : Side,Fin (D.cells side).count × Bool`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev FaceIndex := Σ side : Side,Fin (D.cells side).count × Bool

/--
Defines `cellPoint` of type `ℝ` by `((D.cells side).lo i:ℝ)+(((D.cells side).hi i:ℝ)-((D.cells
side).lo i:ℝ))*z`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def cellPoint (side : Side) (i : Fin (D.cells side).count) (z : ℝ) : ℝ :=
  ((D.cells side).lo i:ℝ)+(((D.cells side).hi i:ℝ)-((D.cells side).lo i:ℝ))*z

/--
Membership in the specified domain/enclosure: `D.cellPoint side i z∈Icc ((D.cells side).lo i:ℝ)
((D.cells side).hi i:ℝ)`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cellPoint_mem (side : Side) (i : Fin (D.cells side).count) {z : ℝ} (hz : z∈Icc (0:ℝ) 1) :
    D.cellPoint side i z∈Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ) := by
  have hp : ((D.cells side).lo i:ℝ)<((D.cells side).hi i:ℝ) := by exact_mod_cast (D.cells side).nonempty i
  unfold cellPoint
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hp.le) hz.1,
    mul_nonneg (sub_nonneg.mpr hp.le) (sub_nonneg.mpr hz.2)]

/--
Constructs witnesses with the exact properties `∃ z∈Icc (0:ℝ) 1,D.cellPoint side i z=t`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cellPoint_surjective (side : Side) (i : Fin (D.cells side).count) {t : ℝ}
    (ht : t∈Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ)) :
    ∃ z∈Icc (0:ℝ) 1,D.cellPoint side i z=t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp : ((D.cells side).lo i:ℝ)<((D.cells side).hi i:ℝ) := by exact_mod_cast (D.cells side).nonempty i
  refine ⟨(t-((D.cells side).lo i:ℝ))/(((D.cells side).hi i:ℝ)-((D.cells side).lo i:ℝ)),
    ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hp).le,
      (div_le_one (sub_pos.mpr hp)).mpr (by linarith [ht.2])⟩,?_⟩
  unfold cellPoint
  field_simp [(sub_pos.mpr hp).ne']
  ring

/--
Defines `faceTheta` of type `ℝ` by `if face then (scales hκ).thetaPlus U T else (scales
hκ).thetaMinus U T`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def faceTheta (face : Bool) {κ : ℝ} (hκ : 0<κ) (U T : ℝ) : ℝ :=
  if face then (scales hκ).thetaPlus U T else (scales hκ).thetaMinus U T

/--
Defines `faceCriterion` of type `ℝ` by `let t := D.cellPoint i.1 i.2.1 p.2.1 let U :=
(p.2.2.1:ℝ) let T := (p.2.2.2:ℝ) let V := (scales p.1.property).V U T let θ := faceTheta i.2.2
p.1.property U T criterion (D.B i.1 p.1.property t U V θ) (D.C i.1 p.1.property t U V θ)
((D.cells i.1).affine i.2.1 t) (D.normalization.certificateL p.1 t)`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def faceCriterion (i : D.FaceIndex) (p : Ioi (0:ℝ) × StabilityBox) : ℝ :=
  let t := D.cellPoint i.1 i.2.1 p.2.1
  let U := (p.2.2.1:ℝ)
  let T := (p.2.2.2:ℝ)
  let V := (scales p.1.property).V U T
  let θ := faceTheta i.2.2 p.1.property U T
  criterion (D.B i.1 p.1.property t U V θ) (D.C i.1 p.1.property t U V θ)
    ((D.cells i.1).affine i.2.1 t) (D.normalization.certificateL p.1 t)

 /--
Continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` uses this continuity
result to prove the eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
k,D.Admissible κ.property`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Cells.cell_inside`,
`«2610.05164v2».DualCertificate.Data.cellPoint_mem`,
`«2610.05164v2».DualCertificate.thetaMinus_joint_continuous` with the arguments shown in the
proof.
-/
theorem faceCriterion_continuous (i : D.FaceIndex) : Continuous (D.faceCriterion i) := by
  -- Establish continuity hregion before using the function at limits or in calculus arguments.
  have hregion : Continuous (fun p : Ioi (0:ℝ) × StabilityBox =>
      (p.1,p.2.2.1,p.2.2.2) : Ioi (0:ℝ) × StabilityBox → FaceDomain) := by fun_prop
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : Ioi (0:ℝ) × StabilityBox => D.cellPoint i.1 i.2.1 p.2.1) := by
    unfold cellPoint
    fun_prop
  have htmem (p : Ioi (0:ℝ) × StabilityBox) : D.cellPoint i.1 i.2.1 p.2.1∈Icc (0:ℝ) 1 :=
    (D.cells i.1).cell_inside i.2.1 (D.cellPoint_mem i.1 i.2.1 p.2.1.property)
  -- Establish continuity hθ before using the function at limits or in calculus arguments.
  have hθ : Continuous (fun p : Ioi (0:ℝ) × StabilityBox => faceTheta i.2.2 p.1.property p.2.2.1 p.2.2.2) := by
    cases he : i.2.2
    · exact thetaMinus_joint_continuous.comp hregion
    · exact thetaPlus_joint_continuous.comp hregion
  have hθmem (p : Ioi (0:ℝ) × StabilityBox) :
      faceTheta i.2.2 p.1.property p.2.2.1 p.2.2.2∈Icc (0:ℝ) 1 := by
    have hb := (scales p.1.property).theta_bounds p.2.2.1.property p.2.2.2.property
    cases i.2.2
    · exact hb.1
    · exact hb.2
  have hV := V_joint_continuous.comp hregion
  have hVmem (p : Ioi (0:ℝ) × StabilityBox) : (scales p.1.property).V p.2.2.1 p.2.2.2∈Icc (0:ℝ) 1 := by
    have hb := (scales p.1.property).V_bounds p.2.2.1.property p.2.2.2.property
    exact ⟨((scales p.1.property).f_nonneg p.2.2.1.property).trans hb.1,hb.2.trans p.2.2.1.property.2⟩
  -- Establish continuity hmap before using the function at limits or in calculus arguments.
  have hmap : Continuous (fun p : Ioi (0:ℝ) × StabilityBox =>
      (p.1,(⟨D.cellPoint i.1 i.2.1 p.2.1,htmem p⟩ : Icc (0:ℝ) 1),p.2.2.1,
        (⟨(scales p.1.property).V p.2.2.1 p.2.2.2,hVmem p⟩ : Icc (0:ℝ) 1),
        (⟨faceTheta i.2.2 p.1.property p.2.2.1 p.2.2.2,hθmem p⟩ : Icc (0:ℝ) 1))) :=
    continuous_fst.prodMk ((ht.subtype_mk _).prodMk
      (continuous_snd.snd.fst.prodMk ((hV.subtype_mk _).prodMk (hθ.subtype_mk _))))
  have hb := (D.normalization.certificateB_joint_continuous D.potential i.1 D.ξ₀ D.ξ₁ D.χ D.τ).comp hmap
  have hc := (D.normalization.centeredC_joint_continuous D.potential i.1).comp hmap
  -- Establish continuity he before using the function at limits or in calculus arguments.
  have he : Continuous (fun p : Ioi (0:ℝ) × StabilityBox =>
      (D.cells i.1).affine i.2.1 (D.cellPoint i.1 i.2.1 p.2.1)) := by unfold Cells.affine;fun_prop
  have hl := D.normalization.certificateL_joint_continuous.comp
    (continuous_fst.prodMk (ht.subtype_mk htmem))
  exact (((psi_c2.continuous.comp (hb.sub he)).sub hc).sub (he.mul (continuous_const.sub hl)))

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k,D.Admissible
κ.property`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_stable` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k,∀ hκ :
0<κ,D.Admissible hκ`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem admissible_stable_subtype (k : Ioi (0:ℝ)) (ha : D.Admissible k.property) :
    ∀ᶠ κ in 𝓝 k,D.Admissible κ.property := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hall : ∀ i : D.FaceIndex,∀ᶠ κ in 𝓝 k,∀ x : StabilityBox,D.faceCriterion i (κ,x)<0 := by
    intro i
    apply positive_compact_strict_stability (D.faceCriterion_continuous i) k
    intro x
    have h := ha i.1 i.2.1 (D.cellPoint i.1 i.2.1 x.1) (D.cellPoint_mem i.1 i.2.1 x.1.property)
      x.2.1 x.2.1.property x.2.2 x.2.2.property
    dsimp only [faceCriterion]
    cases he : i.2.2
    · simpa only [faceTheta,he,Bool.false_eq_true,ite_false] using h.1
    · simpa only [faceTheta,he,ite_true] using h.2
  filter_upwards [Filter.eventually_all.mpr hall] with κ hκ
  intro side i t ht U hU T hT
  obtain ⟨z,hz,he⟩ := D.cellPoint_surjective side i ht
  let x : StabilityBox := (⟨z,hz⟩,⟨U,hU⟩,⟨T,hT⟩)
  have hm := hκ ⟨side,i,false⟩ x
  have hp := hκ ⟨side,i,true⟩ x
  simpa only [faceCriterion,faceTheta,Bool.false_eq_true,ite_false,ite_true,he,x] using And.intro hm hp

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k,∀ hκ :
0<κ,D.Admissible hκ`.

Use: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` uses this bound to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop,∀ J :
«2610.05164v2».Fiber (n+1),D.analytic.targetValue-ε≤J.val.normalizedEnergy`.

Article: 2610.05164v2, Theorem E.1.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.Data.admissible_stable_subtype` with the arguments shown in the
proof.
-/
theorem admissible_stable {k : ℝ} (hk : 0<k) (ha : D.Admissible hk) :
    ∀ᶠ κ in 𝓝 k,∀ hκ : 0<κ,D.Admissible hκ := by
  have hmap : Filter.map (Subtype.val : Ioi (0:ℝ) → ℝ) (𝓝 (⟨k,hk⟩ : Ioi (0:ℝ)))=𝓝 k := by
    rw [map_nhds_subtype_val,nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds hk)]
  rw [← hmap,Filter.eventually_map]
  exact (D.admissible_stable_subtype ⟨k,hk⟩ ha).mono (fun _ h _ => h)

end Data
end
end «2610.05164v2».DualCertificate
