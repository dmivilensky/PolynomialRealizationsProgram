import polyak.Growth.HorizonRate
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: Appendix C, arbitrary restriction-closed classes in Lemma plateauclass.
Use: the class may omit continuations and need not be closed topologically.
Its envelope is the genuine supremum over all finite dimensions and members.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Set Filter
open scoped Topology

structure SegmentClass (A B β : ℝ) (H : ℕ) where
  contains : ∀ d n : ℕ,HSegment (EuclideanSpace ℝ (Fin d)) A B β H n → Prop
  restriction : ∀ d n (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n),contains d n s →
    ∀ l m (h : l+m≤n),contains d m (s.restrict l m h)

namespace SegmentClass
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

def ratios (n : ℕ) : Set ℝ := {r | ∃ d : ℕ,
  ∃ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
    G.contains d n s ∧ stateNorm s.x 0≠0 ∧ r=stateNorm s.x n/stateNorm s.x 0}

def envelope (n : ℕ) : ℝ:=sSup (insert 0 (G.ratios n))

theorem ratios_bddAbove (n : ℕ) : BddAbove (insert 0 (G.ratios n)) := by
  refine ⟨(1+|A|+|B|+|β|)^n,?_⟩
  rintro r (rfl|⟨d,s,_,hs,rfl⟩)
  · positivity
  · exact (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mpr
      (s.stateNorm_le n le_rfl)

theorem envelope_nonneg (n : ℕ) : 0≤G.envelope n:=
  le_csSup (G.ratios_bddAbove n) (mem_insert _ _)

theorem envelope_le (n : ℕ) : G.envelope n≤Growth.FiniteHorizon.envelope A B β H n := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl|⟨d,s,_,hs,rfl⟩)
  · exact Growth.FiniteHorizon.envelope_nonneg A B β H n
  · exact le_csSup (Growth.FiniteHorizon.ratios_bddAbove A B β H n)
      (mem_insert_of_mem _ ⟨d,s,hs,rfl⟩)

theorem stateNorm_le {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (hs : G.contains d n s) : stateNorm s.x n≤G.envelope n*stateNorm s.x 0 := by
  by_cases hz : stateNorm s.x 0=0
  · rw [s.stateNorm_eq_zero_of_zero hz n le_rfl,hz,mul_zero]
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hz))).mp
    exact le_csSup (G.ratios_bddAbove n) (mem_insert_of_mem _ ⟨d,s,hs,hz,rfl⟩)

theorem stateNorm_window_le {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (hs : G.contains d n s) (l p : ℕ) (hp : l+p≤n) :
    stateNorm s.x (l+p)≤G.envelope p*stateNorm s.x l := by
  simpa only [HSegment.stateNorm_restrict,Nat.add_zero] using
    G.stateNorm_le (s.restrict l p hp) (G.restriction d n s hs l p hp)

theorem envelope_submultiplicative (p q : ℕ) : G.envelope (p+q)≤G.envelope p*G.envelope q := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl|⟨d,s,hs,hzero,rfl⟩)
  · exact mul_nonneg (G.envelope_nonneg p) (G.envelope_nonneg q)
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hzero))).mpr
    calc
      _≤G.envelope q*stateNorm s.x p:=G.stateNorm_window_le s hs p q le_rfl
      _≤G.envelope q*(G.envelope p*stateNorm s.x 0):=
        mul_le_mul_of_nonneg_left (by simpa using G.stateNorm_window_le s hs 0 p (by omega))
          (G.envelope_nonneg q)
      _=_:=by ring

theorem tendsto_log_div {r : ℝ} (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => Real.log (G.envelope n)/n) atTop (𝓝 (Real.log r)) := by
  have hh:=(Real.continuousAt_log hr.ne').tendsto.comp hlim
  simpa only [Function.comp_def,Real.log_rpow (hpos _),div_eq_mul_inv,mul_comm] using hh

theorem rate_pow_le {r : ℝ} (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r))
    (n : ℕ) (hn : 0<n) : r^n≤G.envelope n := by
  have hlog:=G.tendsto_log_div hpos hr hlim
  have hadd : Subadditive (fun n => Real.log (G.envelope n)):=by
    intro p q
    calc
      _≤Real.log (G.envelope p*G.envelope q):=
        Real.log_le_log (hpos _) (G.envelope_submultiplicative p q)
      _=_:=Real.log_mul (hpos _).ne' (hpos _).ne'
  have hb : BddBelow (range (fun n : ℕ => Real.log (G.envelope n)/n)):=hlog.bddBelow_range
  have heq : hadd.lim=Real.log r:=tendsto_nhds_unique (hadd.tendsto_lim hb) hlog
  have hlo:=hadd.lim_le_div hb hn.ne'
  rw [heq] at hlo
  have hm:=(le_div_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ)<n)).mp hlo
  rw [←Real.exp_log hr,←Real.exp_nat_mul,←Real.exp_log (hpos n)]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exists_exponential_majorant {r R : ℝ} (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r)) (hR : r<R) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,G.envelope n≤C*R^n := by
  have hRp : 0<R:=hr.trans hR
  have hlogs:=G.tendsto_log_div hpos hr hlim
  have he : Real.log r<Real.log R:=Real.log_lt_log hr hR
  have hn : ∀ᶠ n : ℕ in atTop,G.envelope n≤R^n:=by
    filter_upwards [hlogs.eventually (gt_mem_nhds he),eventually_gt_atTop 0] with n hn hn0
    have hm:=(div_lt_iff₀ (Nat.cast_pos.mpr hn0 : (0 : ℝ)<n)).mp hn
    rw [←Real.exp_log (hpos n),←Real.rpow_natCast,Real.rpow_def_of_pos hRp]
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨N,hN⟩:=eventually_atTop.mp hn
  let C:=1+∑ k∈Finset.range N,G.envelope k/R^k
  have hC : 1≤C:=by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => div_nonneg (hpos k).le (pow_pos hRp k).le)
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N≤n
  · exact (hN n hn).trans (by nlinarith [pow_pos hRp n])
  · have hs : G.envelope n/R^n≤∑ k∈Finset.range N,G.envelope k/R^k:=
      Finset.single_le_sum (fun k _ => div_nonneg (hpos k).le (pow_pos hRp k).le)
        (Finset.mem_range.mpr (by omega))
    apply (div_le_iff₀ (pow_pos hRp n)).mp
    dsimp [C]
    linarith

end SegmentClass
end polyak.FiniteHorizon
