import polyak.FiniteHorizon.ClassProfiles
import Mathlib.Topology.Sequences

/-!
Article: Appendix C, finite sections in Lemma plateauclass.
Use: compactness concerns scalar normalized energy profiles only. Members of
the class are never assumed to extend, and the class need not be closed.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Set Filter Finset
open scoped Topology

namespace SegmentClass
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

def EnergyBound (t K : ℝ) (w : ℕ) : Prop :=
  ∀ d n : ℕ,∀ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,G.contains d n s →
    ∀ i j : ℕ,w≤ i → i≤j → j+w≤n →
      mass (discountedEnergy s.x t) i (j+1)≤K*(energyWindow (discountedEnergy s.x t) w i+
        energyWindow (discountedEnergy s.x t) w j)

def energyProfile (_G : SegmentClass A B β H) {d n : ℕ}
    (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (t : ℝ) (k : ℕ) : ℝ:=if k≤n then discountedEnergy s.x t k/stateNorm s.x 0^2 else 0

theorem energyProfile_nonneg {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (t : ℝ) (k : ℕ) : 0≤G.energyProfile s t k := by
  unfold energyProfile
  split_ifs
  · exact div_nonneg (discountedEnergy_nonneg s.x t k) (sq_nonneg _)
  · exact le_rfl

theorem energyProfile_le {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (hs : G.contains d n s) (t : ℝ) (k : ℕ) : G.energyProfile s t k≤G.profileWeight t k := by
  by_cases hk : k≤n
  · rw [energyProfile,ite_eq_left hk]
    by_cases hz : stateNorm s.x 0=0
    · simp only [hz,zero_pow (by omega : (2 : ℕ)≠0),div_zero]
      exact G.profileWeight_nonneg t k
    · have hzero : 0<stateNorm s.x 0^2:=sq_pos_of_ne_zero hz
      have hx : ‖s.x k‖≤G.envelope k*stateNorm s.x 0:=
        (norm_left_le_stateNorm s.x k).trans (by simpa using G.stateNorm_window_le s hs 0 k (by omega))
      have hsq:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg (G.envelope_nonneg k)
        (stateNorm_nonneg s.x 0))).mpr hx
      apply (div_le_iff₀ hzero).mpr
      have hm:=mul_le_mul_of_nonneg_left hsq (Real.exp_pos (-2*(k : ℝ)*t)).le
      simpa only [discountedEnergy,profileWeight,mul_pow,mul_assoc] using hm
  · rw [energyProfile,ite_eq_right hk]
    exact G.profileWeight_nonneg t k

theorem energyProfile_forward {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (hs : G.contains d n s) (t : ℝ) (i k : ℕ) (hik : i+k≤n) (hi : i+1≤n) :
    G.energyProfile s t (i+k)≤G.profileWeight t k*
      (G.energyProfile s t i+Real.exp (2*t)*G.energyProfile s t (i+1)) := by
  have hx : ‖s.x (i+k)‖≤G.envelope k*stateNorm s.x i:=
    (norm_left_le_stateNorm s.x (i+k)).trans (G.stateNorm_window_le s hs i k hik)
  have hsq:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg (G.envelope_nonneg k)
    (stateNorm_nonneg s.x i))).mpr hx
  have he : Real.exp (-2*((i+k : ℕ) : ℝ)*t)=
      Real.exp (-2*(k : ℝ)*t)*Real.exp (-2*(i : ℝ)*t):=by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  have hbase : discountedEnergy s.x t (i+k)≤G.profileWeight t k*
      (discountedEnergy s.x t i+Real.exp (2*t)*discountedEnergy s.x t (i+1)):=by
    rw [←discounted_stateNorm]
    unfold discountedEnergy profileWeight
    rw [he,mul_pow] at *
    nlinarith [mul_le_mul_of_nonneg_left hsq
      (mul_pos (Real.exp_pos (-2*(k : ℝ)*t)) (Real.exp_pos (-2*(i : ℝ)*t))).le]
  have hm:=div_le_div_of_nonneg_right hbase (sq_nonneg (stateNorm s.x 0))
  simp only [energyProfile,ite_eq_left hik,ite_eq_left hi,ite_eq_left (show i≤n by omega)]
  convert hm using 1
  ring

theorem mass_energyProfile {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (t : ℝ) (i j : ℕ) (hj : j≤n+1) :
    mass (G.energyProfile s t) i j=mass (discountedEnergy s.x t) i j/stateNorm s.x 0^2 := by
  unfold mass
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hh : k≤n:=by have := (mem_Ico.mp hk).2; omega
  simp only [energyProfile,ite_eq_left hh]

theorem energyProfile_energy {t K : ℝ} {w : ℕ} (he : G.EnergyBound t K w)
    {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n) (hs : G.contains d n s)
    (i j : ℕ) (hi : w≤ i) (hij : i≤j) (hjn : j+w≤n) :
    mass (G.energyProfile s t) i (j+1)≤K*(energyWindow (G.energyProfile s t) w i+
      energyWindow (G.energyProfile s t) w j) := by
  have hh:=div_le_div_of_nonneg_right (he d n s hs i j hi hij hjn) (sq_nonneg (stateNorm s.x 0))
  unfold energyWindow at *
  rw [G.mass_energyProfile s t _ _ (by omega),G.mass_energyProfile s t _ _ (by omega),
    G.mass_energyProfile s t _ _ (by omega)]
  convert hh using 1
  ring

theorem energyProfile_state {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
    (t : ℝ) (P : ℕ) (hP : P+1≤n) :
    G.energyProfile s t P+Real.exp (2*t)*G.energyProfile s t (P+1)=
      Real.exp (-2*(P : ℝ)*t)*stateNorm s.x P^2/stateNorm s.x 0^2 := by
  rw [discounted_stateNorm]
  simp only [energyProfile,ite_eq_left hP,ite_eq_left (show P≤n by omega)]
  ring

end SegmentClass
end polyak.FiniteHorizon
