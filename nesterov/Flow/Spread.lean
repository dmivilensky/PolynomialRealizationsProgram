import nesterov.Flow.SpreadGrid
import nesterov.Flow.SpreadScale

/-!
Article: Lemma `lem:spread`, all three inequalities with one finite spectrum.
Use: the frequency scale is chosen first and one midpoint grid last; every
positive real lag is covered, with one strictly positive uniform margin.
-/
namespace nesterov.Flow
noncomputable section
open Set Finset

/-- The complete spread-spectrum conclusion, including the exact midpoint grid. -/
structure SpreadWitness (θ m c : ℝ) where
  J : ℕ
  J_pos : 0<J
  scale : ℝ
  scale_ge_one : 1≤scale
  margin : ℝ
  margin_pos : 0<margin
  margin_le_one : margin≤1
  spectrum : Spectrum (Fin J)
  weight_eq : ∀ j,spectrum.weight j=1/(J:ℝ)
  frequency_eq : ∀ j,spectrum.frequency j=scale*(1+((j:ℝ)+1/2)/(J:ℝ))
  forward : ∀ q : ℝ,0<q →
    margin*spectrum.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
      spectrum.average (fun γ=>forwardKernel θ m c γ q)
  backward : ∀ q : ℝ,0<q →
    margin*spectrum.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
      spectrum.average (fun γ=>backwardKernel θ m c γ q)
  minimizer : 1≤(3*c-θ)*spectrum.average (fun γ=>γ^2)-c*delta θ m c

set_option maxHeartbeats 0 in
/-- A strictly feasible finite midpoint spectrum exists throughout θ/3<c<c_Q. -/
theorem exists_spread {θ m c : ℝ} (hθ : 0<θ) (_hm : 0<m)
    (hc : θ/3<c) (hcQ : c<cQ θ m) : Nonempty (SpreadWitness θ m c) := by
  have hcp : 0<c := by linarith
  obtain ⟨hc2,hδ⟩ := (lt_cQ_iff θ m c).mp hcQ
  have hb : 0<θ-2*c := by linarith
  have hbc : θ-2*c≤c := by linarith
  have hnum : 0<3*c-θ := by linarith
  let a := (3*c-θ)/c
  have ha : 0<a := div_pos hnum hcp
  let d := bufferFloor a
  have hd : 0<d := bufferFloor_pos ha
  let Q : ℝ := max 1 (36/d)
  have hQ : 1≤Q := le_max_left _ _
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hQd : 36≤d*Q := by
    have hh := (div_le_iff₀ hd).mp (le_max_right (1:ℝ) (36/d))
    nlinarith
  obtain ⟨u,hu,hUmin⟩ := spreadU_uniform_positive (a:=1/2) (b:=Q) (by norm_num) (by linarith)
  obtain ⟨γ₀,hg1,hgc,hgQ,hgδ,hgδ1,hgmin,hgmed,hglong⟩ :=
    exists_spread_scale hcp hQ hu hd hδ ha
  have hgp : 0<γ₀ := zero_lt_one.trans_le hg1
  let qIII : ℝ := 2/(a*c)
  have hqIII : 0<qIII := by dsimp [qIII]; positivity
  let X : ℝ := max Q (γ₀*qIII)
  have hX : 0<X := hQp.trans_le (le_max_left _ _)
  let e : ℝ := min (u/2) (d/4)
  have he : 0<e := lt_min (by positivity) (by positivity)
  obtain ⟨J,hJ⟩ := exists_nat_gt ((8+4*X)/e+1)
  have hJp : (0:ℝ)<J := by nlinarith [div_pos (by linarith : 0<8+4*X) he]
  have hJn : 0<J := Nat.cast_pos.mp hJp
  have herr : (8+4*X)/(2*J)≤e := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*J)).mpr
    have hh : (8+4*X)/e<(J:ℝ) := by linarith
    have hh' := (div_lt_iff₀ he).mp hh
    nlinarith [mul_pos he hJp]
  let ν := midpointSpectrum J hJn γ₀ hgp.le
  have hfreq := midpointSpectrum_frequency_bounds hJn hgp.le
  have hfreq' : ∀ j,ν.frequency j≤2*γ₀ := fun j=>(hfreq j).2
  have hfreq0 : ∀ j,γ₀≤ν.frequency j := fun j=>(hfreq j).1
  let K : ℝ := 3/d+(1+2*γ₀/c)/a
  have hK : 0<K := by dsimp [K]; positivity
  let ε : ℝ := min 1 (min (γ₀^2/6) (min (γ₀^2*u/(16*(1+Q)))
    (min (γ₀^2/(4*K)) ((θ-2*c)*γ₀))))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hε1 : ε≤1 := min_le_left _ _
  have hεshort : ε≤γ₀^2/6 := (min_le_right _ _).trans (min_le_left _ _)
  have hεmed : ε≤γ₀^2*u/(16*(1+Q)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεlong : ε≤γ₀^2/(4*K) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεb : ε≤(θ-2*c)*γ₀ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨⟨J,hJn,γ₀,hg1,ε,hε,hε1,ν,fun _=>rfl,fun _=>rfl,?_,?_,?_⟩⟩
  · intro q hq
    have hAB0 : 0≤ν.average (fun γ=>kernelA c γ q+kernelB c γ q) :=
      ν.le_average (fun j=>add_nonneg (kernelA_nonneg _ _ _) (kernelB_nonneg hcp (ν.frequency_nonneg j) hq.le))
    by_cases hshort : q≤1/(2*γ₀)
    · have hh : (γ₀^2/6)*ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
          ν.average (fun γ=>forwardKernel θ m c γ q) := by
        unfold Spectrum.average
        rw [mul_sum]
        apply sum_le_sum
        intro j _
        have ht := forwardKernel_short hcp hb.le hbc hgp hgc (hfreq0 j) (hfreq' j) hq hshort hgδ
        nlinarith only [mul_le_mul_of_nonneg_left ht (ν.weight_nonneg j)]
      exact (mul_le_mul_of_nonneg_right hεshort hAB0).trans hh
    · by_cases hmedium : q≤Q/γ₀
      · have hx0 : 1/2≤γ₀*q := by
          have hh := (div_lt_iff₀ (by positivity : 0<2*γ₀)).mp (lt_of_not_ge hshort)
          nlinarith
        have hxQ : γ₀*q≤Q := by
          have hh := (le_div_iff₀ hgp).mp hmedium
          nlinarith
        have hcq : c*q≤1 := by
          have hh := mul_le_mul_of_nonneg_right hgQ hq.le
          nlinarith
        have herrors := midpoint_UV_error hJn (q:=γ₀*q) (X:=X) (by positivity)
          (hxQ.trans (le_max_left _ _))
        have hUJ : u/2≤midpointAverage J (fun lam=>lam^2*(1-Real.cos (lam*(γ₀*q)))) := by
          have he' := herr.trans (min_le_left (u/2) (d/4))
          have hmin := hUmin _ ⟨hx0,hxQ⟩
          have herr' := (abs_le.mp herrors.1).2
          linarith
        have hUm : γ₀^2*(u/2)≤ν.average (fun γ=>γ^2*(1-Real.cos (γ*q))) := by
          rw [midpointSpectrum_Umoment]
          exact mul_le_mul_of_nonneg_left hUJ (sq_nonneg γ₀)
        have hw := ν.forward_medium_lower hcp hq.le hgp.le hb.le hbc ha.le hδ.le hcq hfreq' hUm
        have hqw : 4*c*γ₀^2*q≤4*c*γ₀*Q := by
          nlinarith [mul_le_mul_of_nonneg_left hxQ (by positivity : 0≤4*c*γ₀)]
        have hW : γ₀^2*u/4≤ν.average (fun γ=>forwardKernel θ m c γ q) := by
          nlinarith only [hw,hgmed,hqw]
        have hAB := ν.average_kernel_medium_upper hcp hq.le hgp.le hcq hfreq'
        have hAB' : ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤4*(1+Q) := by
          nlinarith only [hAB,hxQ]
        have hratio : (γ₀^2*u/(16*(1+Q)))*(4*(1+Q))=γ₀^2*u/4 := by field_simp; ring
        have hh := mul_le_mul_of_nonneg_left hAB' (by positivity : 0≤γ₀^2*u/(16*(1+Q)))
        rw [hratio] at hh
        exact ((mul_le_mul_of_nonneg_right hεmed hAB0).trans hh).trans hW
      · let D := hyperbolicBuffer a c q
        have hfloor : d≤D := bufferFloor_le ha.le (by positivity)
        have hD : 0<D := hd.trans_le hfloor
        have hmom := midpoint_secondMoment_bounds hJn
        have hoscJ : midpointAverage J (fun lam=>lam^2*Real.cos (lam*(γ₀*q)))≤
            D*midpointAverage J (fun lam=>lam^2)/2 := by
          by_cases hlarge : qIII≤q
          · have hD2 : 2≤D := by
              have hs := Real.self_le_sinh_iff.mpr (show 0≤c*q by positivity)
              have hq' := (div_le_iff₀ (mul_pos ha hcp)).mp hlarge
              have hbuf := buffer_sinh_le (a:=a) (c:=c) (q:=q)
              nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
            have hh := (le_abs_self _).trans (midpoint_cosMoment_abs_le hJn (γ₀*q))
            nlinarith [mul_le_mul_of_nonneg_right hD2 (show 0≤midpointAverage J (fun lam=>lam^2) by linarith)]
          · have hxQ : Q≤γ₀*q := by
              have hh := (div_lt_iff₀ hgp).mp (lt_of_not_ge hmedium)
              nlinarith
            have hxX : γ₀*q≤X :=
              (mul_le_mul_of_nonneg_left (le_of_not_ge hlarge) hgp.le).trans (le_max_right _ _)
            have herrors := midpoint_UV_error hJn (q:=γ₀*q) (X:=X) (by positivity) hxX
            have hV := abs_spreadV_le (show 0<γ₀*q by positivity)
            have h9 : 9/(γ₀*q)≤d/4 := by
              apply (div_le_iff₀ (by positivity : 0<γ₀*q)).mpr
              nlinarith [mul_le_mul_of_nonneg_left hxQ hd.le]
            have he' := herr.trans (min_le_right (u/2) (d/4))
            have hupper := (abs_le.mp herrors.2).1
            have hbound := le_abs_self (spreadV (γ₀*q))
            have hh : midpointAverage J (fun lam=>lam^2*Real.cos (lam*(γ₀*q)))≤d/2 := by linarith
            have hdM := mul_le_mul_of_nonneg_left hmom.1 hD.le
            nlinarith
        have hosc : ν.average (fun γ=>γ^2*Real.cos (γ*q))≤
            D*ν.average (fun γ=>γ^2)/2 := by
          rw [midpointSpectrum_cosMoment,midpointSpectrum_secondMoment]
          nlinarith only [mul_le_mul_of_nonneg_left hoscJ (sq_nonneg γ₀)]
        have hW := ν.forward_long_lower hcp hq.le hgp.le hb.le hbc ha hδ.le hd
          hfreq hfloor hosc hglong
        have hAB := ν.average_kernel_upper hcp hq.le hgp.le ha hd hfreq' hfloor
        have hratio : (γ₀^2/(4*K))*K=γ₀^2/4 := by field_simp
        have hh := mul_le_mul_of_nonneg_left hAB (by positivity : 0≤γ₀^2/(4*K))
        change γ₀^2/(4*K)*ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤γ₀^2/(4*K)*(K*D) at hh
        rw [←mul_assoc,hratio] at hh
        exact ((mul_le_mul_of_nonneg_right hεlong hAB0).trans hh).trans hW
  · intro q hq
    exact ν.backward_margin hcp hq.le hgp.le hb.le hε1 hεb hgδ1 hfreq0
  · have hh : γ₀^2≤ν.average (fun γ=>γ^2) :=
      ν.le_average (fun j=>pow_le_pow_left₀ hgp.le (hfreq0 j) 2)
    have hi := mul_le_mul_of_nonneg_left hh hnum.le
    linarith

end
end nesterov.Flow
