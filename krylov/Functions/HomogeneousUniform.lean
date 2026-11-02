import krylov.Functions.HomogeneousSubstitution

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, compact-uniform
general homogeneous substitution.
Use: propagate genuine uniform first jets through a bounded family of
continuous d-linear response maps, with an explicit common radius.
Source: the actual multilinear telescoping estimate; no response conclusion
is an execution field or an assumption.
-/

namespace krylov.Functions
noncomputable section
open Set
variable {d : ℕ} {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A genuine uniform source first jet inherits a bound from the actual
source, without a separately assumed leading-coefficient bound.
Article: main_krylov, lem:cycle-transfer. -/
theorem uniform_jet_leading_bound (x : ℝ → ι → V) (v : ι → V) (U : Set ι)
    (B : ℝ)
    (hx : ∃ εx : ℝ, 0<εx ∧ ∀ ε : ℝ, 0<ε → ε<εx → ∀ u∈U, ‖x ε u‖≤B*ε)
    (hjet : ∀ τ : ℝ, 0<τ → ∃ ετ : ℝ, 0<ετ ∧ ∀ ε : ℝ, 0<ε → ε<ετ →
      ∀ u∈U, ‖x ε u-ε • v u‖≤τ*ε) : ∀ u∈U, ‖v u‖≤B+1 := by
  obtain ⟨ex,hex,hxb⟩ := hx
  obtain ⟨ej,hej,hjb⟩ := hjet 1 (by norm_num)
  let ε := min ex ej/2
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hex' : ε<ex := by dsimp only [ε]; linarith [min_le_left ex ej]
  have hej' : ε<ej := by dsimp only [ε]; linarith [min_le_right ex ej]
  intro u hu
  have hb := hxb ε hε hex' u hu
  have hj := hjb ε hε hej' u hu
  have hn := norm_sub_le (x ε u) (x ε u-ε • v u)
  rw [sub_sub_cancel,norm_smul,Real.norm_of_nonneg hε.le] at hn
  nlinarith only [hn,hb,hj,hε]

/-- Actual uniform first jets remain uniform after every genuine bounded
degree-d multilinear response, for arbitrary index families.
Article: main_krylov, lem:cycle-transfer, general homogeneous degree. -/
theorem uniform_homogeneous_jet
    (P : ι → ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W)
    (x : ℝ → ι → V) (v : ι → V) (U : Set ι) (B C : ℝ)
    (hB : 0≤B) (hC : 0≤C)
    (hP : ∀ u∈U, ‖P u‖≤C) (hv : ∀ u∈U, ‖v u‖≤B)
    (hx : ∃ εx : ℝ, 0<εx ∧ ∀ ε : ℝ, 0<ε → ε<εx → ∀ u∈U, ‖x ε u‖≤B*ε)
    (hjet : ∀ τ : ℝ, 0<τ → ∃ ετ : ℝ, 0<ετ ∧ ∀ ε : ℝ, 0<ε → ε<ετ →
      ∀ u∈U, ‖x ε u-ε • v u‖≤τ*ε) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u∈U,
      ‖homogeneousResponse (P u) (x ε u)-ε^d • homogeneousResponse (P u) (v u)‖≤η*ε^d := by
  intro η hη
  let A := C*d*B^(d-1)
  have hA : 0≤A := by dsimp only [A]; positivity
  let τ := η/(A+1)
  have hτ : 0<τ := by dsimp only [τ]; positivity
  obtain ⟨ex,hex,hxb⟩ := hx
  obtain ⟨ej,hej,hjb⟩ := hjet τ hτ
  refine ⟨min ex ej,lt_min hex hej,?_⟩
  intro ε hε he u hu
  have hb := homogeneousResponse_jet_bound (P u) (x ε u) (v u) ε B τ hε hB
    (hxb ε hε (he.trans_le (min_le_left _ _)) u hu) (hv u hu)
    (hjb ε hε (he.trans_le (min_le_right _ _)) u hu)
  have hcoef : ‖P u‖*d*B^(d-1)*τ≤η := by
    have hp := hP u hu
    have hm : ‖P u‖*d*B^(d-1)*τ≤A*τ := by dsimp only [A]; gcongr
    have heq : (A+1)*τ=η := by dsimp only [τ]; field_simp
    nlinarith only [hm,heq,hτ]
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hε.le d))

end
end krylov.Functions
