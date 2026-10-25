import polyak.Levels.Chart.GapClosure
import polyak.Levels.Chart.DoubleRoot
import polyak.Levels.Chart.AmplitudeFace

/-! Realization and exact phase equations on every finite coordinate face. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set Filter Topology

abbrev ClosedGapParameters (K : ℕ) := {p : ParameterSpace //
  p∈closedRootTriangle K ∧ amplitudeFloor p.2.1 p.2.2<p.1 ∧ -1<p.2.1}

def closedGapCoefficientPoint {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K) : CoefficientPoint :=
  ⟨gapPolynomial p.val.1 p.val.2.1 p.val.2.2,
    gapPolynomial_mem_domain p.property.2.2 p.property.1.2.1
      (p.property.1.2.2.trans_lt (boundaryCosine_succ_lt_one hK)) p.property.2.1⟩

def closedGapInverse {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K) : Tuning :=
  inverseTuning (closedGapCoefficientPoint hK p)

@[simp] theorem coefficients_closedGapInverse {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K) :
    coefficients (closedGapInverse hK p)=gapPolynomial p.val.1 p.val.2.1 p.val.2.2 :=
  coefficients_inverseTuning _

theorem closedGapInverse_beta_pos {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K) :
    0<(closedGapInverse hK p).beta := inverseBeta_pos _

theorem continuous_closedGapInverse {K : ℕ} (hK : 2≤K) : Continuous (closedGapInverse hK) := by
  apply continuous_inverseTuning.comp
  apply Continuous.subtype_mk
  exact continuous_gapPolynomial.comp continuous_subtype_val

theorem boundaryAngle_strict_mem {K : ℕ} (hK : 3≤K) :
    boundaryAngle K∈Ioo (0:ℝ) Real.pi := by
  have hm := boundaryAngle_mem (K:=K) (by omega)
  refine ⟨hm.1,?_⟩
  unfold boundaryAngle
  apply (div_lt_iff₀ (by exact_mod_cast (show 0<K by omega) : 0<(K:ℝ))).mpr
  have hk : (2:ℝ)<K := by exact_mod_cast (show 2<K by omega)
  nlinarith [Real.pi_pos]

theorem root_at_boundary_phase (q : Tuning) {a r₁ r₂ : ℝ} {K : ℕ}
    (hK : 3≤K) (he : coefficients q=gapPolynomial a r₁ r₂)
    (hr : boundaryCosine K=r₁ ∨ boundaryCosine K=r₂) :
    q.angle (2*Real.pi/K)=Real.pi/K := by
  have hh : q.angle (boundaryAngle K)=boundaryAngle K/2 := by
    apply (angle_eq_half_iff_Xi q (boundaryAngle_strict_mem hK)).mpr
    rw [←eval_coefficients,he,gapPolynomial_eval]
    change 1+boundaryCosine K-a*(boundaryCosine K-r₁)*(boundaryCosine K-r₂)=1+boundaryCosine K
    rcases hr with hr|hr <;> rw [hr] <;> ring
  change q.angle (boundaryAngle K)=_
  rw [hh]
  unfold boundaryAngle
  ring

/-- Upper face, upper locked corner, lower face and two-tongue junction. -/
theorem closed_gap_faces {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K) :
    (p.val.2.2=boundaryCosine (K+1) →
      (closedGapInverse hK p).angle (2*Real.pi/(K+1))=Real.pi/(K+1)) ∧
    (3≤K → p.val.2.1=boundaryCosine K →
      (closedGapInverse hK p).angle (2*Real.pi/K)=Real.pi/K) := by
  constructor
  · intro he
    simpa only [Nat.cast_add,Nat.cast_one] using
      root_at_boundary_phase _ (show 3≤K+1 by omega) (coefficients_closedGapInverse hK p) (Or.inr he.symm)
  · intro hk he
    apply root_at_boundary_phase _ hk (coefficients_closedGapInverse hK p)
    exact Or.inl he.symm

theorem junction_phase_equations {K : ℕ} (hK : 3≤K) (p : ClosedGapParameters K)
    (hl : p.val.2.1=boundaryCosine K) (hr : p.val.2.2=boundaryCosine (K+1)) :
    (closedGapInverse (show 2≤K by omega) p).angle (2*Real.pi/K)=Real.pi/K ∧
    (closedGapInverse (show 2≤K by omega) p).angle (2*Real.pi/(K+1))=Real.pi/(K+1) := by
  exact ⟨(closed_gap_faces (show 2≤K by omega) p).2 hK hl,
    (closed_gap_faces (show 2≤K by omega) p).1 hr⟩

theorem diagonal_face_boundary {K : ℕ} (hK : 2≤K) (p : ClosedGapParameters K)
    (hd : p.val.2.1=p.val.2.2) :
    closedGapInverse hK p∈frontier {q : Tuning | Regions.OmegaOne q} := by
  have hu := p.property.1.2.2.trans_lt (boundaryCosine_succ_lt_one hK)
  have ha := (amplitudeFloor_pos (hd ▸ hu) hu).trans p.property.2.1
  have he := coefficients_closedGapInverse hK p
  rw [←hd] at he
  exact (double_root_boundary _ ha ⟨p.property.2.2,hd ▸ hu⟩ he).2.2

/-- The finite K=2 coordinate face is the original quadratic stability line. -/
theorem two_gap_stability_face {ι : Type*} {l : Filter ι} (q : ι→Tuning)
    (p : ι→ParameterSpace) (he : ∀i,coefficients (q i)=gapPolynomial (p i).1 (p i).2.1 (p i).2.2)
    {a r₂ : ℝ} (hp : Tendsto p l (𝓝 (a,(-1:ℝ),r₂))) :
    Tendsto (fun i=>2*(1+(q i).beta)-(q i).y) l (𝓝 0) := by
  apply stability_gap_tendsto_of_coefficients q
    ((continuous_gapPolynomial.continuousAt.tendsto.comp hp).congr (fun i=> (he i).symm))
  rw [gapPolynomial_neg_one]
  ring

end polyak.Levels.Chart
