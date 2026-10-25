import polyak.FareyPlateau.Plateau.RegularClasses
import polyak.FareyPlateau.Plateau.RegularGCD
import polyak.FareyPlateau.Plateau.RegularSlope
import polyak.FareyPlateau.Ray.Reindex
import polyak.FareyPlateau.Ray.Slope
import polyak.ModeLocking.TwoLag.Extension

/-! The dual weights of every actual regular singleton are an admissible
source symbol. This includes resonant slopes and arbitrary certificate periods. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set Filter
open scoped BigOperators Topology

theorem phase_deriv_actual (q : Tuning) (s : ℝ) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) Real.pi) :
    deriv (TwoLag.phase q s) x=deriv (Geometry.shiftedAngle q s) x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact Geometry.jointAngle_actual q s ⟨hy.1.le,hy.2.le⟩

theorem finiteSymbol_deriv_sum (q : Tuning) (s : ℝ) (N : Finset ℤ)
    (w : ℤ→ℝ) {x : ℝ} (hx : x∈Icc (0:ℝ) Real.pi) :
    deriv (finiteSymbol q s N w) x=
      ∑ n∈N,w n*deriv (lagExtension q s n) x := by
  unfold finiteSymbol
  exact (HasDerivAt.fun_sum (fun n _=>
    ((analyticAt_lagExtension q s n hx).differentiableAt.hasDerivAt).const_mul (w n))).deriv

theorem regular_singleton_admissible {q : Tuning} {L j k : ℕ}
    (R : RegularData q 0 L) (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range R.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    Symbols.Admissible k b
      (Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
      (fun n : R.lags=> (n:ℤ)) (fun n=>R.dual n) := by
  classical
  have hbmod : b%(k:ℤ)=b := Int.emod_eq_of_lt hb0.le hbk
  have hbinv : (b*j)%k=1 := by
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
      (by omega : (1:ℤ)<k)] using hb
  refine ⟨Subtype.val_injective,fun n=>R.lags_nonzero n n.property,
    fun n=>R.dual_pos n n.property,?_,?_,?_,?_,?_⟩
  · simpa only [Finset.sum_coe_sort] using R.dual_sum
  · intro n
    rw [hbmod]
    exact (RegularSingleton.lag_classes R hk hj hjk b hb0 hbk hb hS n n.property).symm
  · obtain ⟨n,hn,m,hm,hne,ho,ho'⟩ :=
      RegularSingleton.position_one_pair R hk hj hjk b hb0 hbk hb hS
    exact ⟨⟨n,hn⟩,⟨m,hm⟩,hne,ho.trans hbmod.symm,ho'.trans hbmod.symm⟩
  · have him : (Finset.univ : Finset R.lags).image (fun n : R.lags=>(n:ℤ))=R.lags := by
      ext n
      simp
    rw [Finset.gcd_eq_gcd_image,him]
    exact regular_lags_gcd_one R
  · let ω := Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le
    have hω : (ω:ℝ)∈Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
    have hp : TwoLag.phase q 0 ω=Real.pi/k := by
      rw [TwoLag.phase,Geometry.jointAngle_actual q 0 ω.property]
      exact Edge.singleton_phase_eq R hk hj hjk b hbinv hS
    have ht : (∑n:R.lags,R.dual n *
        deriv (Geometry.extendedLag (TwoLag.phase q 0) (n:ℤ)) ω)=0 := by
      change (∑n:R.lags,R.dual n*deriv (lagExtension q 0 (n:ℤ)) ω)=0
      rw [Finset.sum_coe_sort R.lags (fun n=>R.dual n*deriv (lagExtension q 0 n) ω),
        ←finiteSymbol_deriv_sum q 0 R.lags R.dual ω.property]
      have hh := R.symbol_slope_support ⟨0,R.d_pos⟩
      rw [RegularSingleton.atoms_eq R hk hjk hS] at hh
      exact hh
    have hh := tangency_slope_balance hk hjk.le (TwoLag.analyticAt_phase q 0 ω.property)
      hp b hb0 hbinv (fun n:R.lags=>(n:ℤ)) (fun n=>R.dual n)
      (fun n=>RegularSingleton.lag_classes R hk hj hjk b hb0 hbk hb hS n n.property) ht
    have hd : 2*deriv (TwoLag.phase q 0) ω=
        Ray.edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D := by
      rw [phase_deriv_actual q 0 hω]
      exact Ray.source_slope_index q hj hjk he
    dsimp only [ω] at hd
    simpa only [hbmod,hd] using hh

end polyak.FareyPlateau
