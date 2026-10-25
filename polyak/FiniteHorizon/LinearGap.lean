import polyak.FiniteHorizon.PhysicalFactors
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: Appendix C, the uniform linear gap in Lemma prices.
Use: a genuine boundary derivative smaller than one yields explicit positive
linear minimizer and diagonal corrections, valid even at the critical G=1.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Filter Set
open scoped Topology

theorem exists_linear_lower_gap {f : ℝ → ℝ} {T d : ℝ}
    (hf : HasDerivAt f d T) (hzero : f T=0) (hd : 0<d) :
    ∃ b η : ℝ,0<b ∧ 0<η ∧ ∀ δ : ℝ,0<δ → δ≤η → b*δ≤f (T+δ) := by
  have hsl : ∀ᶠ t in 𝓝[≠] T,d/2<slope f T t:=
    hf.tendsto_slope.eventually (lt_mem_nhds (by linarith : d/2<d))
  obtain ⟨l,r,hT,hsub⟩:=mem_nhds_iff_exists_Ioo_subset.mp (eventually_nhdsWithin_iff.mp hsl)
  refine ⟨d/2,(r-T)/2,by positivity,by linarith [hT.2],?_⟩
  intro δ hδ hδη
  have hh:=hsub (show T+δ∈Ioo l r by constructor <;> linarith [hT.1,hT.2]) (show T+δ≠T by linarith)
  rw [slope_def_field,hzero,sub_zero,add_sub_cancel_left] at hh
  exact ((lt_div_iff₀ hδ).mp hh).le

theorem exists_polyak_linear_margins {V : ℝ → ℝ} {q T v' : ℝ}
    (hV : HasDerivAt V v' T) (hv' : v'<1) (hVT : 0<V T) (heq : T-Real.log q=V T) :
    ∃ a b η : ℝ,0<a ∧ 0<b ∧ 0<η ∧ η≤1 ∧ ∀ δ : ℝ,0<δ → δ≤η →
      0≤Real.sinh (V (T+δ)) ∧
      Real.sinh (V (T+δ))≤Real.sinh (T+δ-Real.log q) ∧
      0≤b*δ/8 ∧ b*δ/8≤1 ∧
      4*(b*δ/8)≤Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2 ∧
      a*δ≤(Real.cosh (T+δ)-1)*
        (Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2)+
          2*(b*δ/8)*Real.sinh (T+δ-Real.log q)^2 := by
  let u:=Real.sinh (V T)
  have hu : 0<u:=Real.sinh_pos_iff.mpr hVT
  let f:=fun t => Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2
  let d:=2*u*Real.cosh (V T)*(1-v')
  have hv'pos : 0<1-v':=by linarith
  have hd : 0<d:=by dsimp [d]; positivity
  have hphy : HasDerivAt (fun t : ℝ => Real.sinh (t-Real.log q)) (Real.cosh (T-Real.log q)) T:=
    by simpa only [Function.comp_def,id_eq,mul_one] using
      (Real.hasDerivAt_sinh (T-Real.log q)).comp T ((hasDerivAt_id T).sub_const _)
  have hbase:=hV.sinh
  have hfd : HasDerivAt f d T:=by
    convert (hphy.pow 2).sub (hbase.pow 2) using 1
    dsimp [d,u]
    rw [heq]
    ring
  have hf0 : f T=0:=by dsimp [f]; rw [heq]; ring
  obtain ⟨b,η,hb,hη,hgap⟩:=exists_linear_lower_gap hfd hf0 hd
  have hbasepos : ∀ᶠ t in 𝓝 T,0<Real.sinh (V t):=
    (Real.continuous_sinh.continuousAt.comp hV.continuousAt).eventually (lt_mem_nhds hu)
  have hphypos : ∀ᶠ t in 𝓝 T,u/2<Real.sinh (t-Real.log q):=
    hphy.continuousAt.eventually (lt_mem_nhds (by
      change u/2<Real.sinh (T-Real.log q)
      rw [heq]
      change u/2<u
      linarith))
  obtain ⟨l,r,hT,hsub⟩:=mem_nhds_iff_exists_Ioo_subset.mp (hbasepos.and hphypos)
  let η':=min η (min ((r-T)/2) (min 1 (8/b)))
  have hr0 : 0<(r-T)/2:=by linarith [hT.2]
  have hη' : 0<η':=by dsimp [η']; positivity
  let a:=b*(u/2)^2/4
  have ha : 0<a:=by dsimp [a]; positivity
  have hη1 : η'≤1:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨a,b,η',ha,hb,hη',hη1,?_⟩
  intro δ hδ hδη
  have hδη0 : δ≤η:=hδη.trans (min_le_left _ _)
  have hδr : δ≤(r-T)/2:=by dsimp [η'] at hδη; exact (hδη.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδb : δ≤8/b:=by
    dsimp [η'] at hδη
    exact hδη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp:=hsub (show T+δ∈Ioo l r by constructor <;> linarith [hT.1,hT.2])
  have hg:=hgap δ hδ hδη0
  change b*δ≤Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2 at hg
  have hγ : 0≤b*δ/8:=by positivity
  have hγ1 : b*δ/8≤1:=by
    have hh:=(le_div_iff₀ hb).mp hδb
    nlinarith
  have hvpos : 0<Real.sinh (T+δ-Real.log q):=by linarith [hp.2]
  have hvsq : (u/2)^2≤Real.sinh (T+δ-Real.log q)^2:=by nlinarith [hp.2]
  have hγv:=mul_le_mul_of_nonneg_left hvsq (show 0≤b*δ/4 by positivity)
  have hG:=Real.one_le_cosh (T+δ)
  have hprod:=mul_nonneg (sub_nonneg.mpr hG)
    (show 0≤Real.sinh (T+δ-Real.log q)^2-Real.sinh (V (T+δ))^2 by nlinarith)
  refine ⟨hp.1.le,by nlinarith [hp.1],hγ,hγ1,by nlinarith,?_⟩
  dsimp [a]
  nlinarith

end polyak.FiniteHorizon
