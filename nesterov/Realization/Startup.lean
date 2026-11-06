import nesterov.Realization.FiniteControl
import nesterov.Realization.Execution
import nesterov.Momentum.Parameters

/-!
Article: Lemma `lem:startup`, the complete finite-dimensional from-rest witness.
Use: the feasible spectral table is repaired at its actual first query and is
then proved equal to the physical executor on one genuine objective for all time.
-/
namespace nesterov.Realization
noncomputable section
open Spectral polyak polyak.Interpolation polyak.Realization Filter Set
open scoped BigOperators NNReal Topology
variable {J : Type*} [Fintype J]

set_option maxHeartbeats 0 in
/-- One objective, one initial point and one auxiliary amplitude realize all
horizons simultaneously, with the prescribed orthogonal wave components. -/
theorem exists_startup (q : Momentum.Tuning) {μ L t C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)
      t (finiteSpectrum w c hw) C)
    (hstrict : 0<t → |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)) :
    ∃ lam∈Ioo μ L,∃ Y : ℝ,∃ f : WithLp 2 (EuclideanSpace ℂ J×ℝ)→ℝ,
      0<Y ∧ CenteredSmoothStronglyConvex μ L f ∧
      Tendsto (fun n=>Y*Momentum.iterate (fun x : ℝ=>lam*x) q.beta q.tau q.stepSize 1 n) atTop (𝓝 0) ∧
      (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0≠0) ∧
      (∀ n,Momentum.iterate (gradient f) q.beta q.tau q.stepSize
        (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0) n=
          physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y n) ∧
      ∃ c₀ : ℝ,0<c₀ ∧ ∀ n : ℕ,c₀*Real.exp ((n:ℝ)*t)*
        ‖physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0‖≤
          ‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize
            (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0) n‖ := by
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  let A := M.symbolPair μ L t
  let W := finiteLatent w c t
  let x := waveQuery W q.tau
  let σ := finiteGradient w c A t
  let v := mixtureValue (finiteSpectrum w c hw) A C t
  have hxeq : x=finitePosition w c A t := by
    funext i
    cases i with
    | none => simp [x,waveQuery]
    | some k =>
      exact (Momentum.method_query q.beta q.tau q.stepSize q.step_pos.ne' W k).symm.trans
        (query_finiteLatent M μ L w c t k)
  have hx : x none=0 := rfl
  have hσ : σ none=0 := finiteGradient_none w c A t
  have hv : v none=0 := mixtureValue_none _ A C t
  have htable : TableFeasible x σ v := by
    rw [hxeq]
    exact (finite_tableFeasible_iff w c hw A C t).mpr hfeas
  have hcontrol := finite_startup_control M μ L w c hw hstrict
  rw [←hxeq] at hcontrol
  obtain ⟨lam,hlam,hlim,η,hη,hgap⟩ := exists_scalar_startup hμL q.step_pos.ne'
    (by linarith [q.tau_nonneg] : 1+q.tau≠0) hs
  let m₀ := (L+μ-2*lam)/(L-μ)
  have hm₀ : |m₀|<1 := normalized_scalar_abs_lt_one hμL hlam
  let a := W 1
  let b := ((L+μ)/(L-μ)) • a-(2/(L-μ)) • firstGradient W q.stepSize
  obtain ⟨Y,ψ,hY,hψ,hdata⟩ := exists_startup_potential hm₀ (scalarQuery q.beta q.tau q.stepSize lam)
    (scalarQuery_zero _ _ _ _) ⟨η,hη,hgap⟩ x σ v htable hx hσ hv hcontrol a b
  let f := denormalizeFunction μ L ψ
  have hf : CenteredSmoothStronglyConvex μ L f := hψ.denormalize hμ hμL
  let G := fun k=>((L+μ)/2) • x (some k)-((L-μ)/2) • σ (some k)
  obtain ⟨ψw,hψw,hwdata⟩ := exists_normalized_interpolant htable none hx hσ hv
  have hW : M.IsTrajectory (gradient (denormalizeFunction μ L ψw)) W :=
    M.isTrajectory_denormalize hμL hψw.differentiable (fun k=>by
      rw [normalized_finiteLatent,query_finiteLatent,←hxeq]
      exact (hwdata (some k)).2.symm)
  have hrec (k : ℕ) : W (k+2)=W (k+1)+q.beta • (W (k+1)-W k)-q.stepSize • G k := by
    have hh := (Momentum.method_trajectory_iff _ q.beta q.tau q.stepSize q.step_pos.ne' W).mp hW k
    change W (k+2)=W (k+1)+q.beta • (W (k+1)-W k)-
      q.stepSize • gradient (denormalizeFunction μ L ψw) (x (some k)) at hh
    rw [(hasGradientAt_denormalize hψw.differentiable _).gradient,(hwdata (some k)).2] at hh
    exact hh
  have hcoef : (L+μ)/2-(L-μ)/2*m₀=lam := by
    dsimp [m₀]
    field_simp [ne_of_gt (sub_pos.mpr hμL)]
    ring
  have hdata' (k : ℕ) : gradient f (repairedQuery W q.beta q.tau q.stepSize lam Y k)=
      WithLp.toLp 2 (if k=0 then firstGradient W q.stepSize else G k,
        lam*(Y*scalarQuery q.beta q.tau q.stepSize lam k)) := by
    have hh := (hasGradientAt_denormalize (μ:=μ) (L:=L) hψ.differentiable
      (repairedQuery W q.beta q.tau q.stepSize lam Y k)).gradient
    change gradient f (repairedQuery W q.beta q.tau q.stepSize lam Y k)=_ at hh
    have hd : gradient ψ (repairedQuery W q.beta q.tau q.stepSize lam Y k)=
        productGradient (correctGradient σ b)
          (scalarPosition (scalarQuery q.beta q.tau q.stepSize lam) Y) m₀ (some k) :=
      (hdata (some k)).2
    rw [hd] at hh
    rw [hh]
    apply WithLp.ofLp_injective 2
    simp only [repairedQuery,productPosition,productGradient,scalarPosition,
      WithLp.ofLp_sub,WithLp.ofLp_smul]
    apply Prod.ext
    · by_cases hk : k=0
      · subst k
        simp only [correctPosition,correctGradient,ite_eq_left]
        change ((L+μ)/2) • a-((L-μ)/2) • b=firstGradient W q.stepSize
        dsimp [b]
        have hc1 : (L-μ)/2*((L+μ)/(L-μ))=(L+μ)/2 := by field_simp [ne_of_gt (sub_pos.mpr hμL)]
        have hc2 : (L-μ)/2*(2/(L-μ))=1 := by field_simp [ne_of_gt (sub_pos.mpr hμL)]
        rw [smul_sub,smul_smul,smul_smul,hc1,hc2,one_smul]
        module
      · have hk' : (some k:Option ℕ)≠some 0 := by simpa
        simp only [correctPosition,correctGradient,ite_eq_right hk',ite_eq_right hk]
        rfl
    · change (L+μ)/2*(Y*scalarQuery q.beta q.tau q.stepSize lam k)-
        (L-μ)/2*(m₀*(Y*scalarQuery q.beta q.tau q.stepSize lam k))=
          lam*(Y*scalarQuery q.beta q.tau q.stepSize lam k)
      nlinarith only [congrArg (fun r : ℝ=>r*(Y*scalarQuery q.beta q.tau q.stepSize lam k)) hcoef]
  have heq := physical_iterate W G q.beta q.tau q.stepSize lam Y q.step_pos.ne' hrec (gradient f) hdata'
  let X₀ := physical W q.beta q.tau q.stepSize lam Y 0
  have hnorm (n : ℕ) : Real.exp (((n+1:ℕ):ℝ)*t)≤‖physical W q.beta q.tau q.stepSize lam Y n‖ := by
    have hh := WithLp.norm_fst_le (EuclideanSpace ℂ J) (physical W q.beta q.tau q.stepSize lam Y n)
    change ‖W (n+1)‖≤‖physical W q.beta q.tau q.stepSize lam Y n‖ at hh
    rw [norm_finiteLatent w c hw] at hh
    exact hh
  have hX : 0<‖X₀‖ := (Real.exp_pos _).trans_le (hnorm 0)
  refine ⟨lam,hlam,Y,f,hY,hf,?_,norm_ne_zero_iff.mp hX.ne',heq,Real.exp t/‖X₀‖,
    div_pos (Real.exp_pos _) hX,fun n=>?_⟩
  · simpa using (scalarIterate_tendsto_zero hs ⟨hlam.1.le,hlam.2.le⟩).const_mul Y
  · rw [heq]
    have hh := hnorm n
    have he : Real.exp (((n+1:ℕ):ℝ)*t)=Real.exp t*Real.exp ((n:ℝ)*t) := by
      rw [Nat.cast_add,add_mul,Real.exp_add]
      simp only [Nat.cast_one,one_mul]
      ring
    rw [he] at hh
    have he' : Real.exp t/‖X₀‖*Real.exp ((n:ℝ)*t)*‖X₀‖=
        Real.exp t*Real.exp ((n:ℝ)*t) := by
      calc
        _ = (Real.exp t/‖X₀‖*‖X₀‖)*Real.exp ((n:ℝ)*t) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hX.ne']
    change Real.exp t/‖X₀‖*Real.exp ((n:ℝ)*t)*‖X₀‖≤_
    rw [he']
    exact hh

/-- The orthogonal startup construction has exactly the article's dimension. -/
theorem startup_real_dimension :
    Module.finrank ℝ (WithLp 2 (EuclideanSpace ℂ J×ℝ))=2*Fintype.card J+1 := by
  rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℂ J×ℝ)).finrank_eq,
    Module.finrank_prod,finite_real_dimension,Module.finrank_self]

end
end nesterov.Realization
