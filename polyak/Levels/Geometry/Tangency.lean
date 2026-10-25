import polyak.Levels.Geometry.NormalizedLag
import polyak.Levels.Geometry.DipTopology
import polyak.Levels.Geometry.DipMass
import polyak.Levels.Geometry.CompactPerturbation

/-! The actual finite strict certificate at a nonperiodic contact. All
endpoint controls are derived from the exact analytic endpoint jets. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

 theorem negative_lag_at_contact (Θ : Curve) {ω : Frequency} {K : ℕ}
    (hK : 2≤K) (hcontact : Θ ω=(ω:ℝ)/2)
    (hlo : 2*Real.pi/(K+1)<(ω:ℝ)) (hhi : (ω:ℝ)<2*Real.pi/K) :
    Θ.lag (-(K:ℤ)) ω<0 := by
  have hk : (0:ℝ)<K:=by exact_mod_cast (show 0<K by omega)
  have hk1 : (0:ℝ)<(K:ℝ)+1:=by positivity
  have hωpos : 0<(ω:ℝ):=by linarith [Θ.pos ω]
  have hlow:= (div_lt_iff₀ hk1).mp hlo
  have hupp:= (lt_div_iff₀ hk).mp hhi
  have hθ : Θ ω≠0:=(Θ.pos ω).ne'
  change Lattice.lagValue (Θ ω) ((-(K:ℤ):ℤ)*(ω:ℝ))<0
  apply (Lattice.signed_lag_neg_iff (Θ.pos ω) (Θ.le_pi ω) (-(K:ℤ))).mpr
  refine ⟨-1,?_,?_⟩
  all_goals
    simp only [Int.cast_neg,Int.cast_natCast,Int.cast_one,neg_mul,sub_neg_eq_add,
      Lattice.xi,Lattice.eta,hcontact]
    field_simp
    nlinarith

 theorem normalizedLag_one_nonpos (q : Tuning) (s : ℝ)
    (hweak : ∀ω : Frequency,(ω:ℝ)/2≤shiftedCurve q s ω) :
    ∀ω,normalizedLag q s 1 ω≤0 := by
  intro ω
  by_cases hz : ω=frequencyZero
  · subst ω
    rw [normalizedLag_zero]
    norm_num only [Int.cast_one]
    linarith [tau_pos q]
  · have hn : (ω:ℝ)≠0:=fun he=>hz (Subtype.ext he)
    have hl : (shiftedCurve q s).lag 1 ω≤0 := by
      rw [Curve.lag_sine]
      have hsin : 0≤Real.sin ((ω:ℝ)/2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ω.property.1]) (by linarith [ω.property.2,Real.pi_pos])
      have harg : (ω:ℝ)/2-shiftedCurve q s ω≤0:=sub_nonpos.mpr (hweak ω)
      have hlo : -Real.pi≤(ω:ℝ)/2-shiftedCurve q s ω:=by linarith [ω.property.1,(shiftedCurve q s).le_pi ω]
      have hs : Real.sin ((ω:ℝ)/2-shiftedCurve q s ω)≤0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le harg hlo
      simpa only [Int.cast_one,one_mul] using mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0:ℝ)≤2) hsin) hs
    rw [normalizedLag,ite_eq_right hz]
    exact div_nonpos_of_nonpos_of_nonneg hl (sq_nonneg _)

 theorem strict_symbol_of_nonperiodic_contact (q : Tuning) (s : ℝ) {ω : Frequency} {K : ℕ}
    (hK : 2≤K) (hweak : ∀ω : Frequency,(ω:ℝ)/2≤shiftedCurve q s ω)
    (hcontact : shiftedCurve q s ω=(ω:ℝ)/2)
    (hlo : 2*Real.pi/(K+1)<(ω:ℝ)) (hhi : (ω:ℝ)<2*Real.pi/K) :
    ∃S : StrictSymbol (shiftedCurve q s) nonzeroLags,
      S.symbol.lags={1,-(K:ℤ)} ∧ S.symbol.weight 1=1 ∧
      0<S.symbol.weight (-(K:ℤ)) := by
  let Θ:=shiftedCurve q s
  have hempty : dip Θ=∅ := by ext x; simp only [dip,mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact not_lt_of_ge (hweak x)
  have hc : ω∈closedDip Θ:=hcontact.le
  obtain ⟨v,hv⟩:=closedDip_singleton_of_dip_empty q s ⟨ω,hc⟩ hempty
  have hvω : v=ω := by have hh:=hc; rw [hv,mem_singleton_iff] at hh; exact hh.symm
  subst v
  let f : C(Frequency,ℝ):=⟨normalizedLag q s 1,continuous_normalizedLag q s 1⟩
  let g : C(Frequency,ℝ):=⟨normalizedLag q s (-(K:ℤ)),continuous_normalizedLag q s (-(K:ℤ))⟩
  have hf : ∀x,f x≤0:=normalizedLag_one_nonpos q s hweak
  have hzero : ∀x,f x=0→x=ω := by
    intro x hx
    by_cases hz : x=frequencyZero
    · subst x
      change normalizedLag q s 1 frequencyZero=0 at hx
      rw [normalizedLag_zero] at hx
      norm_num only [Int.cast_one] at hx
      linarith [tau_pos q]
    · by_contra he
      have hout : x∉closedDip Θ := by rwa [hv,mem_singleton_iff]
      have hlt:=lag_one_neg_outside Θ hout hz
      have hfactor:=lag_eq_sq_mul_normalizedLag q s 1 x
      change normalizedLag q s 1 x=0 at hx
      rw [hx,mul_zero] at hfactor
      linarith
  have hg : ∀x,f x=0→g x<0 := by
    intro x hx
    rw [hzero x hx]
    have hn:=negative_lag_at_contact Θ hK hcontact hlo hhi
    have hw : (ω:ℝ)≠0:=(closedDip_interior_frequency Θ hc).1.ne'
    change normalizedLag q s (-(K:ℤ)) ω<0
    rw [normalizedLag,ite_eq_right (fun he=>hw (congrArg Subtype.val he))]
    exact div_neg_of_neg_of_pos hn (sq_pos_of_ne_zero hw)
  obtain ⟨ε,hε,hεall⟩:=compact_strict_perturbation f g hf hg
  let F : C(Frequency,ℝ):=⟨fun x=>Θ.lag 1 x+ε*Θ.lag (-(K:ℤ)) x,
    (Θ.continuous_lag 1).add (continuous_const.mul (Θ.continuous_lag _))⟩
  have hF : ∀x,F x≤0 := by
    intro x
    change Θ.lag 1 x+ε*Θ.lag (-(K:ℤ)) x≤0
    rw [lag_eq_sq_mul_normalizedLag q s 1 x,lag_eq_sq_mul_normalizedLag q s (-(K:ℤ)) x]
    have hh:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x:ℝ)) (hεall x).le
    change (x:ℝ)^2*(normalizedLag q s 1 x+ε*normalizedLag q s (-(K:ℤ)) x)≤0 at hh
    nlinarith only [hh]
  have hFzero : ∀x,F x=0→x=frequencyZero := by
    intro x hx
    by_contra hz
    have hw : (x:ℝ)≠0:=fun he=>hz (Subtype.ext he)
    have hh:=mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hw) (hεall x)
    change Θ.lag 1 x+ε*Θ.lag (-(K:ℤ)) x=0 at hx
    rw [lag_eq_sq_mul_normalizedLag q s 1 x,lag_eq_sq_mul_normalizedLag q s (-(K:ℤ)) x] at hx
    change (x:ℝ)^2*(normalizedLag q s 1 x+ε*normalizedLag q s (-(K:ℤ)) x)<0 at hh
    nlinarith only [hh,hx]
  let m : C(Frequency,ℝ):=⟨Θ.minimizer,Θ.continuous_minimizer⟩
  obtain ⟨γ,hγ,hγall⟩:=compact_strict_perturbation F m hF (fun x hx=>by
    rw [hFzero x hx]; exact (by norm_num [m,Curve.minimizer_at_zero]))
  have hne : (1:ℤ)≠-(K:ℤ):=by omega
  let S : CertificateSymbol Θ nonzeroLags :=
    { lags:={1,-(K:ℤ)}
      lags_subset:=by intro n hn; simp only [Finset.mem_insert,Finset.mem_singleton] at hn; rcases hn with rfl|rfl <;> simp only [nonzeroLags,mem_ofPred_eq] <;> omega
      weight:=fun n=>if n=1 then 1 else ε
      weight_nonneg:=by intro n _; split <;> positivity
      gamma:=γ
      gamma_nonneg:=hγ.le }
  have hmem : (1:ℤ)∉({-(K:ℤ)} : Finset ℤ) := by simpa only [Finset.mem_singleton] using hne
  have heval : ∀x,S.eval x=F x+γ*m x := by
    intro x
    simp only [CertificateSymbol.eval,S,Finset.sum_insert hmem,
      Finset.sum_singleton,ite_true,ite_eq_right (Ne.symm hne),one_mul,F,m,ContinuousMap.coe_mk]
  have hstrict : ∀x,S.eval x<0:=fun x=>by rw [heval]; exact hγall x
  obtain ⟨a,ha,hmax⟩:=isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set Frequency).Nonempty) S.continuous_eval.continuousOn
  refine ⟨⟨S,-S.eval a,neg_pos.mpr (hstrict a),fun x=>?_⟩,rfl,?_,?_⟩
  · have hh:=hmax (Set.mem_univ x)
    change S.eval x≤S.eval a at hh
    simpa only [neg_neg] using hh
  · simp only [S,ite_true]
  · simp only [S,ite_eq_right (Ne.symm hne)]
    exact hε

end polyak.Levels.Geometry
