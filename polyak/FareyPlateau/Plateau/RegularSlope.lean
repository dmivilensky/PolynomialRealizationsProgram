import polyak.FareyPlateau.Edge.Classes
import polyak.FareyPlateau.Edge.Jets
import polyak.FareyPlateau.Ray.ContactTrigonometry

/-! Tangency of a finite symbol is exactly the source admissibility slope
balance, with both tight classes retained. No sign hypotheses are used. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set
open scoped BigOperators

theorem lag_first_class_formula {j k : ℕ} (hk : 3≤k) (hjk : 2*j≤k)
    {θ : ℝ→ℝ} (hθ : AnalyticAt ℝ θ (Edge.atom j k (by omega) hjk))
    (hp : θ (Edge.atom j k (by omega) hjk)=Real.pi/k)
    (b : ℤ) (hb : (b*j)%k=1) (n : ℤ)
    (hclass : n%(k:ℤ)=0 ∨ n%(k:ℤ)=b) :
    deriv (Geometry.extendedLag θ n) (Edge.atom j k (by omega) hjk)=
      if n%(k:ℤ)=b then
        Real.sin (Real.pi/k)*((n:ℝ)-2*deriv θ (Edge.atom j k (by omega) hjk))
      else -Real.sin (Real.pi/k)*(n:ℝ) := by
  by_cases ho : n%(k:ℤ)=b
  · rw [ite_eq_left ho]
    apply Edge.lag_first_position_one hθ hp n
    rw [hp]
    have htrig := (Edge.lag_trig_reduce (by omega) hjk n (Real.pi/k)).2
    have hprod : (n*j)%k=1 := Ray.residue_product_one hb (by simpa only [ho] using (Int.emod_emod n (k:ℤ)).symm)
    rw [hprod] at htrig
    simp only [Int.cast_one,mul_one] at htrig
    rw [show 2*Real.pi/(k:ℝ)-Real.pi/k=Real.pi/k by ring] at htrig
    exact htrig
  · rw [ite_eq_right ho]
    apply Edge.lag_first_position_zero hθ hp n
    rw [hp]
    have hz : n%(k:ℤ)=0 := hclass.resolve_right ho
    have htrig := (Edge.lag_trig_reduce (by omega) hjk n (Real.pi/k)).2
    rw [Ray.residue_product_zero (j:=j) hz] at htrig
    simpa only [Int.cast_zero,mul_zero,zero_div,zero_sub,Real.sin_neg] using htrig

theorem tangency_slope_balance {I:Type*} [Fintype I]
    {j k : ℕ} (hk : 3≤k) (hjk : 2*j≤k)
    {θ : ℝ→ℝ} (hθ : AnalyticAt ℝ θ (Edge.atom j k (by omega) hjk))
    (hp : θ (Edge.atom j k (by omega) hjk)=Real.pi/k)
    (b : ℤ) (hb0 : 0<b) (hb : (b*j)%k=1) (n:I→ℤ) (w:I→ℝ)
    (hclass : ∀i,n i%(k:ℤ)=0 ∨ n i%(k:ℤ)=b)
    (htan : ∑i,w i*deriv (Geometry.extendedLag θ (n i)) (Edge.atom j k (by omega) hjk)=0) :
    (∑i∈Finset.univ.filter (fun i=>n i%(k:ℤ)=b),
      w i*((n i:ℝ)-2*deriv θ (Edge.atom j k (by omega) hjk)))=
      ∑i∈Finset.univ.filter (fun i=>n i%(k:ℤ)=0),w i*(n i:ℝ) := by
  classical
  have hform : (∑i,w i*deriv (Geometry.extendedLag θ (n i)) (Edge.atom j k (by omega) hjk))=
      Real.sin (Real.pi/k)*
        ((∑i∈Finset.univ.filter (fun i=>n i%(k:ℤ)=b),w i*((n i:ℝ)-2*deriv θ (Edge.atom j k (by omega) hjk)))-
         ∑i∈Finset.univ.filter (fun i=>n i%(k:ℤ)=0),w i*(n i:ℝ)) := by
    simp only [Finset.sum_filter]
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [lag_first_class_formula hk hjk hθ hp b hb (n i) (hclass i)]
    rcases hclass i with hz|ho
    · have hn : n i%(k:ℤ)≠b := by rw [hz]; omega
      simp only [ite_eq_right hn,ite_eq_left hz]
      ring
    · have hn : n i%(k:ℤ)≠0 := by rw [ho]; omega
      simp only [ite_eq_left ho,ite_eq_right hn]
      ring
  have hkr : (3:ℝ)≤k := by exact_mod_cast hk
  have hs : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ (by positivity : (0:ℝ)<k)).mpr (by nlinarith [Real.pi_pos]))
  rw [hform] at htan
  exact sub_eq_zero.mp ((mul_eq_zero.mp htan).resolve_left hs.ne')

end polyak.FareyPlateau
