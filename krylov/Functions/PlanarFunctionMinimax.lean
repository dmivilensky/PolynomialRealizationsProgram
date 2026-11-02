import krylov.Functions.PlanarFiniteRadius

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), actual cubic-function
information lower bound. Use: quantify over every observation-only output
policy, including unbounded policies, and every true binary tensor in the
original diagonal ball. Source: exact indistinguishable scalar cubics and
the proved unrestricted-output finite-scale two-scenario lower bound.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped ENNReal

/-- The actual worst Euclidean gradient of an arbitrary observation-only
output policy over all genuine unit-budget binary cubic functions.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planeCubicPolicyWorst (r p : ℝ) (policy : Observation → Plane) : ℝ≥0∞ :=
  ⨆ t : {t : krylov.Tensor.BinaryCubic // t.InBall},
    ENNReal.ofReal ‖gradient (planeCubicObjective p r t.val) (policy (observe r t.val))‖

/-- Genuine tensor chords approach the actual fibre supremum from below.
Article: main_krylov, thm:Fplanar. -/
theorem exists_chord_near_fibreMinimax (r η : ℝ) (hη : 0<η) :
    ∃ t u : krylov.Tensor.BinaryCubic, Chord r t u ∧ fibreMinimax r-η<chordValue r t u := by
  classical
  by_contra hn
  push Not at hn
  have hb : fibreMinimax r≤fibreMinimax r-η := by
    apply csSup_le ⟨0,zero_mem_chordValues r⟩
    rintro a ⟨t,u,h,rfl⟩
    exact hn t u h
  linarith

/-- Every unrestricted actual output policy has the sharp leading planar
function information lower coefficient, uniformly before the policy and
cycle scale are chosen. Article: main_krylov, prop:Fcycle(iii).
The genuine p⁴ two-function remainder is absorbed into an arbitrarily small
loss in the true M_F coefficient. No bounded-policy hypothesis is used. -/
theorem planeCubicPolicyWorst_lower (r : ℝ) (hr : 0<r) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      ∀ policy : Observation → Plane,
      ENNReal.ofReal (r^2/4*Real.sqrt (1+4*r^2)*(fibreMinimax r-η)*p^3)≤
        planeCubicPolicyWorst r p policy := by
  intro η hη
  by_cases hsmall : fibreMinimax r≤η
  · refine ⟨1,by norm_num,?_⟩
    intro p hp _ policy
    have hn : r^2/4*Real.sqrt (1+4*r^2)*(fibreMinimax r-η)*p^3≤0 := by
      have hmf : fibreMinimax r-η≤0 := by linarith only [hsmall]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hmf) (by positivity)
    rw [ENNReal.ofReal_of_nonpos hn]
    exact bot_le
  · have hMF : η<fibreMinimax r := lt_of_not_ge hsmall
    obtain ⟨t,u,hchord,hvalue⟩ := exists_chord_near_fibreMinimax r (η/2) (by positivity)
    have hv : 0<chordValue r t u := by linarith only [hvalue,hMF,hη]
    have hd : u.t2-t.t2≠0 := by
      intro he
      have hsame : t.t2-u.t2=0 := by linarith only [he]
      unfold chordValue at hv
      rw [hsame,abs_zero,mul_zero,zero_div] at hv
      exact lt_irrefl _ hv
    have hobs := chord_observations hchord
    obtain ⟨C,hC,hlower⟩ := planeCubic_all_output_chord_lower r t u hobs hd hr.ne'
    let K := r^2/4*Real.sqrt (1+4*r^2)
    have hK : 0<K := by dsimp only [K]; positivity
    let ε₀ := min 1 (K*η/(2*(C+1)))
    have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
    refine ⟨ε₀,hε₀,?_⟩
    intro p hp he policy
    have hp₁ : p≤1 := (he.trans_le (min_le_left _ _)).le
    have herror : C*p^4≤K*η/2*p^3 := by
      have hh := (lt_div_iff₀ (by positivity : 0<2*(C+1))).mp (he.trans_le (min_le_right _ _))
      have hpp := mul_le_mul_of_nonneg_right hh.le (by positivity : 0≤p^3)
      have hp₄ : (0:ℝ)≤p^4 := by positivity
      nlinarith only [hpp,hp₄]
    have hb := hlower p hp hp₁ (policy (observe r t))
    have hcoef : K*(fibreMinimax r-η)*p^3≤
        r^2/4*chordValue r t u*Real.sqrt (1+4*r^2)*p^3-C*p^4 := by
      have hh := mul_le_mul_of_nonneg_left hvalue.le (by positivity : 0≤K*p^3)
      dsimp only [K] at hh herror ⊢
      nlinarith only [hh,herror]
    apply (ENNReal.ofReal_le_ofReal (hcoef.trans hb)).trans
    rw [ENNReal.ofReal_max]
    apply max_le
    · exact le_iSup_of_le ⟨t,hchord.1⟩ le_rfl
    · have hh := le_iSup_of_le (i:=⟨u,hchord.2.1⟩)
        (f:=fun t : {t : krylov.Tensor.BinaryCubic // t.InBall}=>
          ENNReal.ofReal ‖gradient (planeCubicObjective p r t.val) (policy (observe r t.val))‖) le_rfl
      simpa only [←hobs] using! hh

end
end krylov.Functions
