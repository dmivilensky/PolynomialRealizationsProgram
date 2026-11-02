import krylov.Stability.ObservedProjection
import krylov.Stability.UniformLineSearch

/-!
Article: main_krylov, apB:lem:UAsteps, uniform actual projected direction and line bounds.
Use: turn genuine old-image conjugacy and weighted true old-span changes
into explicit exact-search stability, without a smallest reference energy.
Source: actual orthogonal projection, the proved observed Gram/conjugacy
bounds and the true weighted exact-line stability inequality.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ}

/-- A real direction whose shifted gradient lies in the actual observed span has the exact source projection decomposition.
Use: actual FC coefficients imply the span hypothesis; no direction expansion is assumed.
Article: main_krylov, apB:lem:UAsteps, D=−(I−P)Ag+PD.
Proof: the genuine old-span projection fixes the actual span displacement;
its true linearity rearranges the real direction equation. -/
theorem observedProjection_decomposition (s : Fin p → E) (H : E →L[ℝ] E) (g d : E)
    (hspan : d+H g∈Submodule.span ℝ (Set.range s)) :
    d= -(H g-observedProjection s (H g))+observedProjection s d := by
  have hp := (Submodule.span ℝ (Set.range s)).starProjection_eq_self_iff.mpr hspan
  change observedProjection s (d+H g)=d+H g at hp
  rw [map_add] at hp
  calc
    d = (d+H g)-H g := by abel
    _ = (observedProjection s d+observedProjection s (H g))-H g := congrArg (fun v => v-H g) hp.symm
    _ = _ := by abel

/-- The true actual old-span projection complement is bounded independently of all observed lengths.
Use: a relaxed uniform constant suffices for the finite direction induction, including an empty old span.
Article: main_krylov, apB:lem:UAsteps.
Proof: use the actual projection contraction and the triangle inequality. -/
theorem observedProjection_complement_bound (s : Fin p → E) (v : E) :
    ‖v-observedProjection s v‖≤2*‖v‖ := by
  have hp := (Submodule.span ℝ (Set.range s)).norm_starProjection_apply_le v
  change ‖observedProjection s v‖≤‖v‖ at hp
  exact (norm_sub_le _ _).trans (by change ‖v‖+‖observedProjection s v‖≤2*‖v‖; linarith)

/-- A true observed-span direction with a small real projected component has uniform actual direction and projected-direction bounds.
Use: absorb genuine approximate conjugacy without dividing by any current or reference direction length.
Article: main_krylov, apB:lem:UAsteps.
Proof: apply the exact real projection decomposition; contraction bounds
the complement, and a projected fraction at most one half is absorbed in
the actual direction norm inequality. -/
theorem projected_direction_bound (s : Fin p → E) (H : E →L[ℝ] E) (g d : E)
    (hspan : d+H g∈Submodule.span ℝ (Set.range s)) {ν : ℝ} (hν : 0≤ν) (hsmall : ν≤1/2)
    (hproj : ‖observedProjection s d‖≤ν*‖d‖) :
    ‖d‖≤4*‖H‖*‖g‖ ∧ ‖observedProjection s d‖≤4*ν*‖H‖*‖g‖ := by
  -- The actual projection is applied to the real span displacement before its small component is absorbed.
  have hd := observedProjection_decomposition s H g d hspan
  have hcomp := (observedProjection_complement_bound s (H g)).trans
    (mul_le_mul_of_nonneg_left (H.le_opNorm g) (by norm_num : (0 : ℝ)≤2))
  have hn : ‖d‖≤2*‖H‖*‖g‖+ν*‖d‖ := by
    calc
      _ = ‖-(H g-observedProjection s (H g))+observedProjection s d‖ := congrArg norm hd
      _ ≤ ‖H g-observedProjection s (H g)‖+‖observedProjection s d‖ := by
        simpa only [norm_neg] using norm_add_le (-(H g-observedProjection s (H g))) (observedProjection s d)
      _ ≤ _ := (add_le_add hcomp hproj).trans_eq (by ring)
  have hnorm : ‖d‖≤4*‖H‖*‖g‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg d)]
  exact ⟨hnorm,hproj.trans ((mul_le_mul_of_nonneg_left hnorm hν).trans_eq (by ring))⟩

/-- True weighted old-span projection changes control the actual direction difference with explicit uniform constants.
Use: the true reference error norm stays attached to its projection change, eliminating a smallest reference-energy denominator.
Article: main_krylov, apB:lem:UAsteps.
Proof: subtract the genuine reference projected direction from the actual
span decomposition. Bound the real gradient change, the weighted true
projection change, and the already absorbed actual old-span component. -/
theorem projected_direction_difference (s : Fin p → E) (H P₀ : E →L[ℝ] E) (g g₀ d d₀ : E)
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    (hd₀ : d₀= -(H g₀-P₀ (H g₀))) {ν ε : ℝ} (hν : 0≤ν) (hsmall : ν≤1/2)
    (hproj : ‖observedProjection s d‖≤ν*‖d‖)
    (hweight : ‖g₀‖*‖observedProjection s-P₀‖≤ε) :
    ‖d-d₀‖≤2*‖H‖*‖g-g₀‖+‖H‖*ε+4*ν*‖H‖*‖g‖ := by
  -- Keep the true reference gradient norm paired with its actual projection difference.
  have hp := (projected_direction_bound s H g d hspan hν hsmall hproj).2
  have he : d-d₀= -(H (g-g₀)-observedProjection s (H (g-g₀)))+
      (observedProjection s-P₀) (H g₀)+observedProjection s d := by
    conv_lhs => rw [observedProjection_decomposition s H g d hspan]
    rw [hd₀]
    simp only [map_sub,_root_.sub_apply]
    abel
  have hc := (observedProjection_complement_bound s (H (g-g₀))).trans
    (mul_le_mul_of_nonneg_left (H.le_opNorm (g-g₀)) (by norm_num : (0 : ℝ)≤2))
  have hw : ‖(observedProjection s-P₀) (H g₀)‖≤‖H‖*ε := by
    calc
      _ ≤ ‖observedProjection s-P₀‖*‖H g₀‖ := (observedProjection s-P₀).le_opNorm _
      _ ≤ ‖observedProjection s-P₀‖*(‖H‖*‖g₀‖) :=
        mul_le_mul_of_nonneg_left (H.le_opNorm g₀) (norm_nonneg _)
      _ = ‖H‖*(‖g₀‖*‖observedProjection s-P₀‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight (norm_nonneg H)
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add (by simpa only [norm_neg] using hc) hw)) hp).trans_eq (by ring))

/-- Actual unit observed pairs, genuine weighted old-span changes and real exact search give the full explicit uniform line-step bound.
Use: the new direction error is derived from actual conjugacy and projection, rather than supplied as a trajectory-closeness hypothesis.
Article: main_krylov, apB:lem:UAsteps, perturbed conjugacy and line steps.
Proof: the actual observed Gram and pair errors give a true projected
conjugacy bound. Absorb it in the real direction comparison, then apply
the proved weighted exact-search perturbation inequality. The reference
gradient/direction weight cancels before any small direction is divided by. -/
theorem observed_lineStep_stability (s y : Fin p → E) (H P₀ B : E →L[ℝ] E)
    (g g₀ d d₀ : E) (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    (hd₀ : d₀= -(H g₀-P₀ (H g₀))) (hd : d≠0) (hd₀nz : d₀≠0) (hgd : ‖g₀‖≤‖d₀‖)
    {η ζ ε : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt p*η≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0)
    (hweight : ‖g₀‖*‖observedProjection s-P₀‖≤ε)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ζ) (hζ : ζ≤1/2) :
    ‖lineLength g d (B d) • d-lineLength g₀ d₀ d₀ • d₀‖≤
      (2+8*‖H‖)*‖g-g₀‖+2*ζ*‖g₀‖+4*‖H‖*ε+64*Real.sqrt p*η*‖H‖*‖g‖ := by
  have hproj := observedProjection_conjugacy_bound s y hs hG d hη hy ho
  have hD := projected_direction_difference s H P₀ g g₀ d d₀ hspan hd₀ (by positivity) hsmall
    (hproj.trans_eq (by ring)) hweight
  have hline := lineStep_stability B g g₀ d d₀ hd hd₀nz hgd hB hζ
  exact hline.trans (by nlinarith)

end
end krylov.Stability
