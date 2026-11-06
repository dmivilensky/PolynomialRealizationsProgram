import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-!
Article: Appendix A, equivalence of trajectory descriptions and from-rest rates.
Use: fixed multiplicative constants disappear under nth roots; strict bounds on
literal limsup factors give a single geometric constant for every horizon.
-/
namespace nesterov.Rates
noncomputable section
open Filter
open scoped Topology

theorem tendsto_const_root {C : ℝ} (hC : 0<C) :
    Tendsto (fun n : ℕ => C^((n:ℝ)⁻¹)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_zero,Function.comp_def] using
    (Real.continuousAt_const_rpow (a:=C) (b:=0) (ne_of_gt hC)).tendsto.comp hinv

/-- Comparison of literal root limsups under a horizon-independent factor. -/
theorem limsup_root_le_of_mul_bound {f g : ℕ → ℝ} {C r : ℝ}
    (hf : ∀ n,0≤f n) (hg : ∀ n,0≤g n) (hC : 0<C)
    (hbound : ∀ n,f n≤C*g n)
    (hlim : Tendsto (fun n : ℕ => g n^((n:ℝ)⁻¹)) atTop (𝓝 r)) :
    limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop≤r := by
  have hmajorant := (tendsto_const_root hC).mul hlim
  simp only [one_mul] at hmajorant
  have hpoint (n : ℕ) : f n^((n:ℝ)⁻¹)≤C^((n:ℝ)⁻¹)*g n^((n:ℝ)⁻¹) := by
    calc
      _ ≤ (C*g n)^((n:ℝ)⁻¹) := Real.rpow_le_rpow (hf n) (hbound n) (by positivity)
      _ = _ := Real.mul_rpow hC.le (hg n)
  have hh := limsup_le_limsup (Eventually.of_forall hpoint)
    (isCoboundedUnder_le_of_le atTop (fun n => Real.rpow_nonneg (hf n) _))
    hmajorant.isBoundedUnder_le
  rwa [hmajorant.limsup_eq] at hh

/-- The same comparison when both genuine root limits have already been proved. -/
theorem root_limit_le_of_mul_bound {f g : ℕ → ℝ} {C r s : ℝ}
    (hf : ∀ n,0≤f n) (hg : ∀ n,0≤g n) (hC : 0<C)
    (hbound : ∀ n,f n≤C*g n)
    (hlimf : Tendsto (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop (𝓝 r))
    (hlimg : Tendsto (fun n : ℕ => g n^((n:ℝ)⁻¹)) atTop (𝓝 s)) : r≤s := by
  have hh := limsup_root_le_of_mul_bound hf hg hC hbound hlimg
  rwa [hlimf.limsup_eq] at hh

/-- A strict limsup upper bound gives a single positive all-horizon constant.
Boundedness is explicit, so a totalized unbounded real limsup cannot be used. -/
theorem exists_mul_pow_of_limsup_root_lt {f : ℕ → ℝ} {R : ℝ}
    (hf : ∀ n,0≤f n)
    (hb : IsBoundedUnder (·≤·) atTop (fun n : ℕ => f n^((n:ℝ)⁻¹)))
    (hR : 0<R) (hlim : limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop<R) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,f n≤C*R^n := by
  have hevent := eventually_lt_of_limsup_lt hlim hb
  have hpowers : ∀ᶠ n : ℕ in atTop,f n≤R^n := by
    filter_upwards [hevent,eventually_gt_atTop 0] with n hn hn0
    calc
      _ = (f n^((n:ℝ)⁻¹))^n := (Real.rpow_inv_natCast_pow (hf n) (by omega)).symm
      _ ≤ R^n := pow_le_pow_left₀ (Real.rpow_nonneg (hf n) _) hn.le n
  obtain ⟨N,hN⟩ := eventually_atTop.mp hpowers
  let C : ℝ := 1+∑ k ∈ Finset.range N,f k/R^k
  have hC : 1≤C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => div_nonneg (hf k) (pow_pos hR k).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N≤n
  · exact (hN n hn).trans (by nlinarith [pow_pos hR n])
  · have hs : f n/R^n≤∑ k ∈ Finset.range N,f k/R^k :=
      Finset.single_le_sum (fun k _ => div_nonneg (hf k) (pow_pos hR k).le)
        (Finset.mem_range.mpr (by omega))
    apply (div_le_iff₀ (pow_pos hR n)).mp
    dsimp [C]
    linarith

/-- A uniform geometric majorant proves the claimed literal root-limsup bound. -/
theorem limsup_root_le_of_mul_pow {f : ℕ → ℝ} {C R : ℝ}
    (hf : ∀ n,0≤f n) (hC : 0<C) (hR : 0<R) (hbound : ∀ n,f n≤C*R^n) :
    limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop≤R := by
  apply limsup_root_le_of_mul_bound hf (fun n => (pow_pos hR n).le) hC hbound
  apply tendsto_congr' (eventually_atTop.mpr ⟨1,fun n hn => ?_⟩) |>.mpr tendsto_const_nhds
  exact Real.pow_rpow_inv_natCast hR.le (by omega)

/-- Geometric majorants also establish the needed boundedness of root factors. -/
theorem roots_bounded_of_mul_pow {f : ℕ → ℝ} {C R : ℝ}
    (hf : ∀ n,0≤f n) (hC : 0<C) (hR : 0<R) (hbound : ∀ n,f n≤C*R^n) :
    IsBoundedUnder (·≤·) atTop (fun n : ℕ => f n^((n:ℝ)⁻¹)) := by
  have hfactor := tendsto_const_root hC
  have hlim : Tendsto (fun n : ℕ => C^((n:ℝ)⁻¹)*R) atTop (𝓝 R) := by
    simpa using hfactor.mul_const R
  apply hlim.isBoundedUnder_le.mono_le
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc
    _ ≤ (C*R^n)^((n:ℝ)⁻¹) := Real.rpow_le_rpow (hf n) (hbound n) (by positivity)
    _ = C^((n:ℝ)⁻¹)*R := by
      rw [Real.mul_rpow hC.le (pow_pos hR n).le,Real.pow_rpow_inv_natCast hR.le (by omega)]

/-- A bounded sequence of nonnegative root factors has nonnegative limsup. -/
theorem root_limsup_nonneg {f : ℕ → ℝ} (hf : ∀ n,0≤f n)
    (hb : IsBoundedUnder (·≤·) atTop (fun n : ℕ => f n^((n:ℝ)⁻¹))) :
    0≤limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop := by
  apply le_limsup_of_le hb
  intro b hbound
  obtain ⟨n,hn⟩ := hbound.exists
  exact (Real.rpow_nonneg (hf n) _).trans hn

/-- A fixed linear combination of two neighboring nonnegative outputs cannot
increase their asymptotic root limsup. -/
theorem neighbor_root_limsup_le {f g : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n,0≤f n) (hg : ∀ n,0≤g n)
    (hbg : IsBoundedUnder (·≤·) atTop (fun n : ℕ => g n^((n:ℝ)⁻¹)))
    (ha : 0≤a) (hb : 0≤b) (hf0 : f 0≤1)
    (hbound : ∀ n,f (n+1)≤a*g (n+1)+b*g n) :
    limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop≤
      limsup (fun n : ℕ => g n^((n:ℝ)⁻¹)) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro R hR
  have hRp : 0<R := (root_limsup_nonneg hg hbg).trans_lt hR
  obtain ⟨C,hC,hgC⟩ := exists_mul_pow_of_limsup_root_lt hg hbg hRp hR
  let K : ℝ := 1+a*C+b*C/R
  have hK : 1≤K := by
    dsimp [K]
    linarith [mul_nonneg ha hC.le,div_nonneg (mul_nonneg hb hC.le) hRp.le]
  apply limsup_root_le_of_mul_pow hf (zero_lt_one.trans_le hK) hRp
  intro n
  cases n with
  | zero => simpa only [pow_zero,mul_one] using hf0.trans hK
  | succ n =>
    calc
      _ ≤ a*g (n+1)+b*g n := hbound n
      _ ≤ a*(C*R^(n+1))+b*(C*R^n) :=
        add_le_add (mul_le_mul_of_nonneg_left (hgC _) ha)
          (mul_le_mul_of_nonneg_left (hgC _) hb)
      _ = (a*C+b*C/R)*R^(n+1) := by
        rw [pow_succ]
        field_simp [ne_of_gt hRp]
      _ ≤ K*R^(n+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_pos hRp _).le
        dsimp [K]
        linarith

/-- A stable first-order reconstruction filter adds at most its own pole to
the asymptotic root factor. All bounds hold on the original finite horizons. -/
theorem filter_root_limsup_le_max {f g : ℕ → ℝ} {p : ℝ}
    (hf : ∀ n,0≤f n) (hg : ∀ n,0≤g n)
    (hbf : IsBoundedUnder (·≤·) atTop (fun n : ℕ => f n^((n:ℝ)⁻¹)))
    (hp : 0≤p) (hg0 : g 0≤1) (hbound : ∀ n,g (n+1)≤f (n+1)+p*g n) :
    limsup (fun n : ℕ => g n^((n:ℝ)⁻¹)) atTop≤
      max (limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop) p := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro R hR
  have hfR : limsup (fun n : ℕ => f n^((n:ℝ)⁻¹)) atTop<R :=
    (le_max_left _ _).trans_lt hR
  have hpR : p<R := (le_max_right _ _).trans_lt hR
  have hRp : 0<R := hp.trans_lt hpR
  obtain ⟨C,hC,hfC⟩ := exists_mul_pow_of_limsup_root_lt hf hbf hRp hfR
  let K : ℝ := 1+C*R/(R-p)
  have hK : 1≤K := by
    dsimp [K]
    linarith [div_nonneg (mul_pos hC hRp).le (sub_pos.mpr hpR).le]
  have hcoef : C*R+p*K≤K*R := by
    have he : (K-1)*(R-p)=C*R := by
      dsimp [K]
      field_simp [ne_of_gt (sub_pos.mpr hpR)]
      ring
    nlinarith
  apply limsup_root_le_of_mul_pow hg (zero_lt_one.trans_le hK) hRp
  intro n
  induction n with
  | zero => simpa only [pow_zero,mul_one] using hg0.trans hK
  | succ n ih =>
    calc
      _ ≤ f (n+1)+p*g n := hbound n
      _ ≤ C*R^(n+1)+p*(K*R^n) :=
        add_le_add (hfC _) (mul_le_mul_of_nonneg_left ih hp)
      _ = (C*R+p*K)*R^n := by rw [pow_succ]; ring
      _ ≤ (K*R)*R^n := mul_le_mul_of_nonneg_right hcoef (pow_pos hRp _).le
      _ = K*R^(n+1) := by rw [pow_succ]; ring

end
end nesterov.Rates
