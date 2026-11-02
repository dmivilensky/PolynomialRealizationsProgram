import krylov.Functions.HomogeneousUniform

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, general degree lift.
Use: combine a genuine operator degree-d expansion with actual uniform
source first jets, proving the extra degree from true gradient scaling.
The only response remainder hypothesis is about the independent operator
map. No native execution or native output expansion is assumed.
Source: the proved genuine multilinear substitution and triangle inequality.
-/

/-!
Article: krylov, Lemma E.5 [lem:cycle-transfer].

The generic homogeneous substitution theorem produces degree d+1 from a degree-d operator
response. Native finite FC/RFC scalar executors supply localized queries and genuine tensor
jets.
The operator polynomial and its remainder are hypotheses of this transfer lemma, exactly as in
the article; localization and reference-replacement estimates are separately derived from
actual searches.
-/

namespace krylov.Functions
noncomputable section
open Set
variable {d : ℕ} {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual scalar rescaling used by finite gradient-homogeneous operator
executors. Article: main_krylov, lem:cycle-transfer. -/
def rescaledOperatorOutput (F : ι → V → W) (x : ℝ → ι → V) (ε : ℝ) (u : ι) : W :=
  ε • F u (x ε u)

/-- A genuine uniform degree-d operator response lifts to degree d+1 after
actual input first-jet substitution and actual gradient scaling.
Article: main_krylov, lem:cycle-transfer, arbitrary homogeneous degree.
Every source size and source jet in the hypotheses is an input statement;
the native output conclusion is derived from an independent operator map. -/
theorem homogeneous_cycle_transfer
    (F : ι → V → W) (P : ι → ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W)
    (x : ℝ → ι → V) (v : ι → V) (U : Set ι) (B C : ℝ)
    (hB : 0≤B) (hC : 0≤C)
    (hP : ∀ u∈U, ‖P u‖≤C) (hv : ∀ u∈U, ‖v u‖≤B)
    (hx : ∃ εx : ℝ, 0<εx ∧ ∀ ε : ℝ, 0<ε → ε<εx → ∀ u∈U, ‖x ε u‖≤B*ε)
    (hjet : ∀ τ : ℝ, 0<τ → ∃ ετ : ℝ, 0<ετ ∧ ∀ ε : ℝ, 0<ε → ε<ετ →
      ∀ u∈U, ‖x ε u-ε • v u‖≤τ*ε)
    (hop : ∀ τ : ℝ, 0<τ → ∃ δ : ℝ, 0<δ ∧ ∀ u∈U, ∀ z : V, ‖z‖<δ →
      ‖F u z-homogeneousResponse (P u) z‖≤τ*‖z‖^d) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u∈U,
      ‖rescaledOperatorOutput F x ε u-ε^(d+1) • homogeneousResponse (P u) (v u)‖≤η*ε^(d+1) := by
  intro η hη
  let τ := η/(2*(B^d+1))
  have hτ : 0<τ := by dsimp only [τ]; positivity
  obtain ⟨δ,hδ,hopb⟩ := hop τ hτ
  obtain ⟨ex,hex,hxb⟩ := hx
  obtain ⟨ej,hej,hjb⟩ := uniform_homogeneous_jet P x v U B C hB hC hP hv ⟨ex,hex,hxb⟩ hjet
    (η/2) (by positivity)
  let ε₀ := min ex (min ej (δ/(B+1)))
  refine ⟨ε₀,by dsimp only [ε₀]; positivity,?_⟩
  intro ε hε he u hu
  have hxe := hxb ε hε (he.trans_le (min_le_left _ _)) u hu
  have hj := hjb ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  have hsmall : ‖x ε u‖<δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<B+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hxe,hh,hε]
  have ho := hopb u hu (x ε u) hsmall
  have hcoef : τ*B^d≤η/2 := by
    have hh : 2*(B^d+1)*τ=η := by dsimp only [τ]; field_simp
    nlinarith only [hh,hτ]
  have hopscaled : ‖F u (x ε u)-homogeneousResponse (P u) (x ε u)‖≤(η/2)*ε^d := by
    calc
      _ ≤ τ*‖x ε u‖^d := ho
      _ ≤ τ*(B*ε)^d := by gcongr
      _ = (τ*B^d)*ε^d := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hε.le d)
  have hn : ‖F u (x ε u)-ε^d • homogeneousResponse (P u) (v u)‖≤η*ε^d := by
    have heq : F u (x ε u)-ε^d • homogeneousResponse (P u) (v u) =
        (F u (x ε u)-homogeneousResponse (P u) (x ε u))+
          (homogeneousResponse (P u) (x ε u)-ε^d • homogeneousResponse (P u) (v u)) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hopscaled hj).trans_eq (by ring))
  have heq : rescaledOperatorOutput F x ε u-ε^(d+1) • homogeneousResponse (P u) (v u) =
      ε • (F u (x ε u)-ε^d • homogeneousResponse (P u) (v u)) := by
    simp only [rescaledOperatorOutput,smul_sub,smul_smul,pow_succ]
    congr 2
    ring
  rw [heq,norm_smul,Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left hn hε.le).trans_eq (by rw [pow_succ]; ring)

end
end krylov.Functions
