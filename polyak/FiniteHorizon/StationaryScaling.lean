import polyak.FiniteHorizon.PricesStationary

/-!
Article: Appendix C, all stationary window centers in Lemma exactprice(c).
Use: covariance of the genuine mixture Gram entries and prescribed values
transfers the proved Y_H reserve to every stationary window Y_k, k≥H.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Spectral Waves Duality MeasureTheory
open scoped BigOperators

theorem stationaryMatrixMap_shift (t : ℝ) (k i j : ℕ) (c : Frequency) :
    stationaryMatrixMap t (k+i) (k+j) c=Real.exp (2*(k : ℝ)*t)*stationaryMatrixMap t i j c := by
  rw [stationaryMatrixMap_eq,stationaryMatrixMap_eq]
  have hs : (((k+i : ℕ) : ℝ)+((k+j : ℕ) : ℝ))*t=2*(k : ℝ)*t+((i : ℝ)+(j : ℝ))*t:=by
    push_cast
    ring
  have hd : ((k+i : ℕ) : ℝ)-((k+j : ℕ) : ℝ)=(i : ℝ)-(j : ℝ):=by
    push_cast
    ring
  rw [hs,hd,Real.exp_add]
  ring

theorem inner_mixturePosition_shift (ν : Spectrum) (t : ℝ) (k i j : ℕ) :
    inner ℝ (mixturePosition ν t (some (k+i))) (mixturePosition ν t (some (k+j)))=
      Real.exp (2*(k : ℝ)*t)*inner ℝ (mixturePosition ν t (some i)) (mixturePosition ν t (some j)) := by
  simp only [mixturePosition,inner_lift]
  change (∫ c,stationaryMatrixMap t (k+i) (k+j) c ∂ν)=
    Real.exp (2*(k : ℝ)*t)*(∫ c,stationaryMatrixMap t i j c ∂ν)
  simp_rw [stationaryMatrixMap_shift,integral_const_mul]

theorem mixtureValue_shift (ν : Spectrum) (m : C(Frequency,ℂ)) (C t : ℝ) (k i : ℕ) :
    mixtureValue ν m C t (some (k+i))=Real.exp (2*(k : ℝ)*t)*mixtureValue ν m C t (some i) := by
  simp only [mixtureValue_some]
  have hs : 2*((k+i : ℕ) : ℝ)*t=2*(k : ℝ)*t+2*(i : ℝ)*t:=by push_cast; ring
  rw [hs,Real.exp_add]
  ring

theorem stationaryHRun_window_shift {A B β T C : ℝ} {H : ℕ} (hB : B≠0) (ν : Spectrum)
    (h : FiniteFeasible (multiplierMap A B β T) T H ν C) (k : ℕ) :
    runWindow (stationaryHRun hB ν h) (H+k)=
      Real.exp (2*(k : ℝ)*T) • stationaryWindow ν (multiplierMap A B β T) C T H := by
  have hidx : H+k-H=k:=by omega
  apply Prod.ext
  · ext i j
    change inner ℝ (mixturePosition ν T (some (H+k-H+i))) (mixturePosition ν T (some (H+k-H+j)))=
      Real.exp (2*(k : ℝ)*T)*inner ℝ (mixturePosition ν T (some i.val)) (mixturePosition ν T (some j.val))
    rw [hidx,inner_mixturePosition_shift]
  · ext i
    change mixtureValue ν (multiplierMap A B β T) C T (some (H+k-H+(i+1)))=
      Real.exp (2*(k : ℝ)*T)*mixtureValue ν (multiplierMap A B β T) C T (some (i+1))
    rw [hidx,mixtureValue_shift]

theorem stationary_price_lower_all_centers {A B β T C : ℝ} {H : ℕ}
    (hB : B≠0) (hH : 5≤H) (ν : Spectrum)
    (h : FiniteFeasible (multiplierMap A B β T) T H ν C) (L : WindowPrice H)
    (hreserve : Real.exp (2*(H-5 : ℕ)*T)/2≤L (stationaryWindow ν (multiplierMap A B β T) C T H))
    (k : ℕ) (hk : H≤k) :
    Real.exp (2*(k-5 : ℕ)*T)/2≤L (runWindow (stationaryHRun hB ν h) k) := by
  obtain ⟨l,rfl⟩:=Nat.exists_eq_add_of_le hk
  rw [stationaryHRun_window_shift,map_smul,smul_eq_mul]
  have he : Real.exp (2*(H+l-5 : ℕ)*T)=
      Real.exp (2*(l : ℝ)*T)*Real.exp (2*(H-5 : ℕ)*T):=by
    rw [←Real.exp_add]
    congr 1
    rw [show H+l-5=(H-5)+l by omega,Nat.cast_add]
    ring
  rw [he]
  have hh:=mul_le_mul_of_nonneg_left hreserve (Real.exp_pos (2*(l : ℝ)*T)).le
  nlinarith

end polyak.FiniteHorizon
