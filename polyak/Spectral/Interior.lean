import polyak.Spectral.Rate
import polyak.Boundary.Tail

/-!
Article: Appendix A, monotonicity in the twist and the actual optimal boundary.
Use: a strictly smaller nonnegative twist is locally feasible when t≠0, with the same spectrum.
Proof: every lag acquires a positive mean-D reserve; a uniform analytic tail leaves
only finitely many continuous strict inequalities to check locally.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Article: nonzero-time radial reserve. Use: every positive lag becomes strictly slack after shrinking twist. -/
theorem meanD_pos (ν : Spectrum) {t : ℝ} (ht : t≠0) (n : ℕ) (hn : 1 ≤ n) :
    0<meanD ν t n := by
  have hT : avg ν (fun c => chebT n c) ≤ 1 := by
    have hi := integrable_continuous ν ((continuous_chebT n).comp continuous_subtype_val)
    calc
      _ ≤ avg ν (fun _ => (1 : ℝ)) := integral_mono hi (integrable_const _)
        (fun c => by
          have hh := lagD_nonneg 0 n c
          simp only [mul_zero,Real.cosh_zero,lagD] at hh
          change chebT n c ≤ 1
          linarith)
      _ = _ := avg_const _ _
  have hn' : (n : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
  have hh := Real.one_lt_cosh.mpr (mul_ne_zero hn' ht)
  unfold meanD
  linarith

/-- Article: strict twist shrink. Use: obtain one strictly feasible infinite system with a fixed scaled C. -/
theorem FeasibleU.strict_scale {u u' t C : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C)
    (ht : t≠0) (hu' : 0 ≤ u') (hu'u : u'<u) :
    ∃ C' : ℝ, |C'|<meanG ν u' ∧ ∀ n : ℕ,1 ≤ n →
      0<meanA ν u' t n-meanB ν u' n+C'*Real.sinh (n*t) ∧
      0<meanA ν u' t n+meanB ν u' n-C'*Real.sinh (n*t) := by
  have hu : 0<u := lt_of_le_of_lt hu' hu'u
  let θ := u'/u
  have hθ₀ : 0 ≤ θ := div_nonneg hu' hu.le
  have hθ₁ : θ<1 := (div_lt_one hu).mpr hu'u
  have he : θ*u=u' := div_mul_cancel₀ _ (ne_of_gt hu)
  have hsq : 0<u^2-u'^2 := by nlinarith
  refine ⟨θ*C,?_,fun n hn => ?_⟩
  · have hab : |θ*C| ≤ |C| := by
      rw [abs_mul,abs_of_nonneg hθ₀]
      exact mul_le_of_le_one_left (abs_nonneg _) hθ₁.le
    have hG : meanG ν u<meanG ν u' := by unfold meanG; linarith
    exact hab.trans_lt (h.1.trans_lt hG)
  · have hD := meanD_pos ν ht n hn
    have hinc : 0<(u^2-u'^2)*meanD ν t n := mul_pos hsq hD
    have ha := h.meanA_nonneg n hn
    have hrest := mul_nonneg (sub_nonneg.mpr hθ₁.le) ha
    obtain ⟨hl,hr⟩ := h.2 n hn
    have hll := mul_nonneg hθ₀ hl
    have hrr := mul_nonneg hθ₀ hr
    have hA := meanA_mul ν θ u t n
    have hB := meanB_mul ν θ u n
    rw [he] at hA hB
    constructor <;> nlinarith

/-- Article: a deliberately coarse radial tail bound. Use: a finite cutoff uniform in a neighborhood of nonzero t. -/
theorem abs_le_two_cosh (x : ℝ) : |x| ≤ 2*Real.cosh x := by
  have he := Real.add_one_le_exp |x|
  have hp := Real.exp_pos (-|x|)
  rw [← Real.cosh_abs x,Real.cosh_eq]
  linarith

/-- Article: a finite strict prefix is locally feasible. Use: isolate continuity from the uniform tail argument. -/
theorem strict_lags_nhds (ν : Spectrum) {u t C : ℝ}
    (hlags : ∀ n : ℕ,1 ≤ n →
      0<meanA ν u t n-meanB ν u n+C*Real.sinh (n*t) ∧
      0<meanA ν u t n+meanB ν u n-C*Real.sinh (n*t)) (N : ℕ) :
    ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t), ∀ n : Fin (N+1),1 ≤ (n : ℕ) →
      0<meanA ν p.1 p.2 n-meanB ν p.1 n+C*Real.sinh (n*p.2) ∧
      0<meanA ν p.1 p.2 n+meanB ν p.1 n-C*Real.sinh (n*p.2) := by
  apply eventually_all.mpr
  intro n
  by_cases hn : 1 ≤ (n : ℕ)
  · have hA := continuous_meanA (ν := fun _ : ℝ×ℝ => ν) continuous_const continuous_fst continuous_snd n
    have hB := continuous_meanB (ν := fun _ : ℝ×ℝ => ν) continuous_const continuous_fst n
    have hC : Continuous (fun p : ℝ×ℝ => C*Real.sinh ((n : ℝ)*p.2)) := by fun_prop
    have hl : ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t),
        0<meanA ν p.1 p.2 n-meanB ν p.1 n+C*Real.sinh (n*p.2) :=
      ((hA.sub hB).add hC).continuousAt.eventually (lt_mem_nhds (hlags n hn).1)
    have hr : ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t),
        0<meanA ν p.1 p.2 n+meanB ν p.1 n-C*Real.sinh (n*p.2) :=
      ((hA.add hB).sub hC).continuousAt.eventually (lt_mem_nhds (hlags n hn).2)
    filter_upwards [hl,hr] with p hl hr using fun _ => ⟨hl,hr⟩
  · exact Eventually.of_forall (fun _ h => (hn h).elim)

/-- Article: one neighborhood and one cutoff control all remaining lags.
Use: the analytic tail does not rely on continuity of an infinite conjunction. -/
theorem uniform_tail_nhds (ν : Spectrum) {u t C : ℝ} (ht : t≠0)
    (hstar : |C|<meanG ν u) :
    ∃ N : ℕ, ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t), |C| ≤ meanG ν p.1 ∧
      ∀ n : ℕ,N<n →
        0 ≤ meanA ν p.1 p.2 n-meanB ν p.1 n+C*Real.sinh (n*p.2) ∧
        0 ≤ meanA ν p.1 p.2 n+meanB ν p.1 n-C*Real.sinh (n*p.2) := by
  let m := meanG ν u-|C|
  let s := |t|/2
  let H := meanG ν u+2*u^2+1
  have hm : 0<m := sub_pos.mpr hstar
  have hs : 0<s := half_pos (abs_pos.mpr ht)
  obtain ⟨N,hN⟩ := exists_nat_gt (4*H/(m*s))
  have hNs : 4*H<(N : ℝ)*(m*s) := (div_lt_iff₀ (mul_pos hm hs)).mp hN
  have hgcont : Continuous (fun p : ℝ×ℝ => meanG ν p.1-|C|) :=
    (continuous_meanG continuous_const continuous_fst).sub continuous_const
  have hhcont : Continuous (fun p : ℝ×ℝ => meanG ν p.1+2*p.1^2) :=
    (continuous_meanG continuous_const continuous_fst).add (continuous_const.mul (continuous_fst.pow 2))
  have hgnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t),m/2<meanG ν p.1-|C| :=
    hgcont.continuousAt.eventually (lt_mem_nhds (by dsimp [m]; linarith))
  have hhnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t),meanG ν p.1+2*p.1^2<H :=
    hhcont.continuousAt.eventually (gt_mem_nhds (by dsimp [H]; linarith))
  have htnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t),s < |p.2| :=
    continuous_snd.abs.continuousAt.eventually (lt_mem_nhds (by dsimp [s]; linarith [abs_pos.mpr ht]))
  refine ⟨N,?_⟩
  filter_upwards [hgnear,hhnear,htnear] with p hgp hHp htp
  refine ⟨by linarith,fun n hnN => ?_⟩
  have hn : 1 ≤ n := by omega
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr (by omega)
  have hc := abs_le_two_cosh ((n : ℝ)*p.2)
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)] at hc
  have hns := mul_le_mul_of_nonneg_right hn' hs.le
  have hnt := mul_le_mul_of_nonneg_left htp.le (Nat.cast_nonneg n)
  have hcosh : (N : ℝ)*s ≤ 2*Real.cosh (n*p.2) := by linarith
  have hrad : meanG ν p.1+2*p.1^2 ≤ (meanG ν p.1-|C|)*Real.cosh (n*p.2) := by
    have hh₁ := mul_le_mul_of_nonneg_left hcosh hm.le
    have hh₂ := mul_le_mul_of_nonneg_right hgp.le (Real.cosh_pos (n*p.2)).le
    nlinarith
  have htail := Boundary.raw_lag_tail_both ν p.1 C p.2 n hn
  exact ⟨by linarith [htail.1],by linarith [htail.2]⟩

/-- Article: strict infinite feasibility is locally open away from t=0.
Use: only a finite prefix uses continuity; every remaining lag follows from one uniform raw-tail bound. -/
theorem feasibleU_nhds_of_strict (ν : Spectrum) {u t C : ℝ} (ht : t≠0)
    (hstar : |C|<meanG ν u)
    (hlags : ∀ n : ℕ,1 ≤ n →
      0<meanA ν u t n-meanB ν u n+C*Real.sinh (n*t) ∧
      0<meanA ν u t n+meanB ν u n-C*Real.sinh (n*t)) :
    ∀ᶠ p : ℝ×ℝ in 𝓝 (u,t), FeasibleU p.1 p.2 ν C := by
  obtain ⟨N,hnear⟩ := uniform_tail_nhds ν ht hstar
  filter_upwards [hnear,strict_lags_nhds ν hlags N] with p hp hpref
  refine ⟨hp.1,fun n hn => ?_⟩
  by_cases hnN : n ≤ N
  · exact ⟨(hpref ⟨n,by omega⟩ hn).1.le,(hpref ⟨n,by omega⟩ hn).2.le⟩
  · exact hp.2 n (by omega)

/-- Article: a strictly smaller nonnegative twist is locally feasible.
Use: the same measure and one fixed rescaled C work throughout a neighborhood. -/
theorem Feasible.interior_mono {v v' t C : ℝ} {ν : Spectrum} (h : Feasible v t ν C)
    (ht : t≠0) (hv' : 0 ≤ v') (hv : v'<v) :
    ∃ C' : ℝ, ∀ᶠ p : ℝ×ℝ in 𝓝 (v',t), Feasible p.1 p.2 ν C' := by
  obtain ⟨C',hstar,hlags⟩ := FeasibleU.strict_scale (u := Real.sinh v) (u' := Real.sinh v') h ht
    (by simpa using Real.sinh_le_sinh.mpr hv') (Real.sinh_lt_sinh.mpr hv)
  have hnear := feasibleU_nhds_of_strict ν ht hstar hlags
  have hc : Continuous (fun p : ℝ×ℝ => (Real.sinh p.1,p.2)) :=
    (Real.continuous_sinh.comp continuous_fst).prodMk continuous_snd
  have hct : Tendsto (fun p : ℝ×ℝ => (Real.sinh p.1,p.2)) (𝓝 (v',t)) (𝓝 (Real.sinh v',t)) :=
    hc.continuousAt
  exact ⟨C',hct.eventually hnear⟩

/-- Article: the actual optimal point lies on the twist boundary when its exponent is nonzero.
Use: links the attained actual maximum T to V before the finite-support argument. -/
theorem actual_boundary {q : ℝ} (hq : 0<q) (ht : T q≠0) (hv : 0<T q-Real.log q) :
    T q-Real.log q=V (T q) := by
  have hle : T q-Real.log q ≤ V (T q) := by
    obtain ⟨ν,C,h⟩ := T_mem hq
    exact (isGreatest_V _).2 ⟨ν,C,h⟩
  apply le_antisymm hle
  by_contra hnot
  have hlt : T q-Real.log q<V (T q) := lt_of_not_ge hnot
  obtain ⟨ν,C,h⟩ := V_mem (T q)
  obtain ⟨C',hnear⟩ := h.interior_mono ht hv.le hlt
  have hc : Continuous (fun s : ℝ => (s-Real.log q,s)) :=
    (continuous_id.sub continuous_const).prodMk continuous_id
  have hevent : ∀ᶠ s : ℝ in 𝓝 (T q), Feasible (s-Real.log q) s ν C' := hc.continuousAt.eventually hnear
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let s := T q+ε/2
  have hs : T q<s := by dsimp [s]; linarith
  have hdist : dist s (T q)<ε := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hs)]
    dsimp [s]
    linarith
  have hmax := (isGreatest_T hq).2 (show s ∈ exponents q from ⟨ν,C',hball hdist⟩)
  linarith

end
end polyak.Spectral
