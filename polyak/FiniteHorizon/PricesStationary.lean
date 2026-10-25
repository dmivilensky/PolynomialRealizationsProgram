import polyak.FiniteHorizon.PricesActual
import polyak.FiniteHorizon.StationaryRun

/-!
Article: Appendix C, the stationary lower bound in Lemma exactprice.
Use: actual finite-memory stationary mixture runs have exactly exponential
radial energy. The proved finite energy bound gives the uniform one-half lower
bound for every feasible probability spectrum and every common value C.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality
open scoped BigOperators

theorem stationaryHRun_window {A B β T C : ℝ} {H : ℕ} (hB : B≠0) (ν : Spectrum)
    (h : FiniteFeasible (multiplierMap A B β T) T H ν C) :
    runWindow (stationaryHRun hB ν h) H=stationaryWindow ν (multiplierMap A B β T) C T H := by
  apply Prod.ext
  · change Matrix.gram ℝ (fun i : Fin (H+2) => mixturePosition ν T (some (H-H+i)))=_
    simp only [Nat.sub_self,Nat.zero_add,stationaryWindow]
  · ext i
    change mixtureValue ν (multiplierMap A B β T) C T (some (H-H+(i+1)))=_
    simp only [Nat.sub_self,Nat.zero_add,stationaryWindow]

theorem stationary_discounted_energy_term (H i : ℕ) (hH : 5≤H) (T δ : ℝ) :
    Real.exp (-2*(T+δ))^i*Real.exp ((H+i-5 : ℕ)*T)^2=
      Real.exp (-2*δ)^i*Real.exp (2*(H-5 : ℕ)*T) := by
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  have he : H+i-5=H-5+i:=by omega
  rw [he,Nat.cast_add]
  ring

theorem windowPrice7_stationary_lower {A B β T a δ ε : ℝ} {H : ℕ}
    {C : WindowMatrix7} {d : ℕ → ℝ} (data : BandedData7 C d ε)
    (hB : B≠0) (ha : 0<a) (hδ : 0<δ) (hε : ε=a*δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp (T+δ))
    (hsource : BandedSource7.{0} A B β (T+δ) H C d)
    (ν : Spectrum) (c : ℝ) (hfeas : FiniteFeasible (multiplierMap A B β T) T H ν c) :
    Real.exp (2*(H-5 : ℕ)*T)/2≤
      windowPrice7 data H a (T+δ) (stationaryWindow ν (multiplierMap A B β T) c T H) := by
  let r:=stationaryHRun hB ν hfeas
  apply stationary_price_half_bound hδ (Real.exp_pos _).le
  intro N
  have hb:=windowPrice7_run_finite_bound data hB ha hδ.le hε hH hRate hsource r H le_rfl N
  rw [stationaryHRun_window hB ν hfeas] at hb
  change δ*(∑ i∈Finset.range N,Real.exp (-2*(T+δ))^i*
    ‖mixturePosition ν T (some (H+i-5))‖^2)≤_ at hb
  simp_rw [norm_mixturePosition,stationary_discounted_energy_term H _ (by omega) T δ] at hb
  exact hb

end polyak.FiniteHorizon
