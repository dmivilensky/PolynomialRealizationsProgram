import polyak.Global.Circle.Phase
import polyak.Levels.Lattice.Atoms
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! A feasible single harmonic must have a primitive finite period.
This rules out irrational witnesses as well as every unenumerated denominator. -/
noncomputable section
namespace polyak.Farey.Examples
open Levels MeasureTheory Set
open Global

theorem single_atom_finite_order {Θ:Curve} {ω:Levels.Frequency}
    (hw:ProgramSolution Θ nonzeroLags (Measure.dirac ω)) :
    IsOfFinAddOrder ((ω:ℝ):Global.Circle) := by
  by_contra hn
  have hd : DenseRange (fun n:ℤ=>n•((ω:ℝ):Global.Circle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by
      rintro ⟨r,hr⟩
      exact hn (AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mpr ⟨r,hr⟩))
  have hp : Function.Periodic (fun _:ℝ=>Θ ω) (2*Real.pi):=by intro x; rfl
  let F:Global.Circle→ℂ:=Circle.wave (fun _:ℝ=>Θ ω) hp 1
  have hc : Continuous (fun x=>(F x).re):=
    Complex.continuous_re.comp (Circle.wave_continuous hp continuous_const 1)
  have hlag:∀n:ℤ,Real.cos ((n:ℝ)*(ω:ℝ)-Θ ω)≤Real.cos (Θ ω) := by
    intro n
    by_cases hn:n=0
    · simp only [hn,Int.cast_zero,zero_mul,zero_sub,Real.cos_neg,le_refl]
    · have hh:=(Lattice.dirac_program_iff Θ nonzeroLags ω).mp hw |>.2 n hn
      exact sub_nonneg.mp hh
  have hr : range (fun n:ℤ=>n•((ω:ℝ):Global.Circle))⊆{x | (F x).re≤Real.cos (Θ ω)} := by
    rintro x ⟨n,rfl⟩
    change (Circle.wave (fun _:ℝ=>Θ ω) hp 1 (n•Circle.ofReal ω)).re≤_
    rw [←map_zsmul,Circle.wave_ofReal,Kernels.cis_re]
    simpa only [Int.cast_one,one_mul,zsmul_eq_mul] using hlag n
  have hall : closure (range (fun n:ℤ=>n•((ω:ℝ):Global.Circle)))⊆
      {x | (F x).re≤Real.cos (Θ ω)}:=closure_minimal hr (isClosed_le hc continuous_const)
  have hh := hall (show Circle.ofReal (Θ ω)∈closure (range (fun n:ℤ=>n•((ω:ℝ):Global.Circle))) by
    rw [hd.closure_range]; exact mem_univ _)
  change (Circle.wave (fun _:ℝ=>Θ ω) hp 1 (Circle.ofReal (Θ ω))).re≤_ at hh
  rw [Circle.wave_ofReal,Kernels.cis_re] at hh
  simp only [Int.cast_one,one_mul,sub_self,Real.cos_zero] at hh
  have hcos : Real.cos (Θ ω)<1 := by
    have h:=Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩ ⟨(Θ.pos ω).le,Θ.le_pi ω⟩ (Θ.pos ω)
    simpa only [Real.cos_zero] using h
  linarith

theorem single_atom_rational {Θ:Curve} {ω:Levels.Frequency}
    (hw:ProgramSolution Θ nonzeroLags (Measure.dirac ω)) :
    ∃j k:ℕ,1≤j ∧ 2*j<k ∧ j.Coprime k ∧ (ω:ℝ)=2*Real.pi*j/k := by
  have hmin:0≤Θ.minimizer ω:=((Lattice.dirac_program_iff Θ nonzeroLags ω).mp hw).1
  have hω0:0<(ω:ℝ) := by
    by_contra hn
    have he:ω=frequencyZero:=Subtype.ext (le_antisymm (le_of_not_gt hn) ω.property.1)
    rw [he,Θ.minimizer_at_zero] at hmin
    norm_num at hmin
  have hωπ:(ω:ℝ)<Real.pi := by
    by_contra hn
    have he:ω=frequencyPi:=Subtype.ext (le_antisymm ω.property.2 (le_of_not_gt hn))
    rw [he,Θ.minimizer_at_pi] at hmin
    norm_num at hmin
  obtain ⟨r,hr⟩ := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mp (single_atom_finite_order hw)
  have hrpos:0<r:=by exact_mod_cast (show (0:ℝ)<r by rw [hr]; positivity)
  have hnum:0<r.num:=Rat.num_pos.mpr hrpos
  have hcast:((r.num.natAbs:ℕ):ℝ)=(r.num:ℝ):=by
    rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg (show (0:ℝ)≤r.num by exact_mod_cast hnum.le)]
  have hkR:0<(r.den:ℝ):=by exact_mod_cast r.pos
  have he:(ω:ℝ)=2*Real.pi*r.num.natAbs/r.den := by
    rw [Rat.cast_def] at hr
    rw [hcast]
    field_simp at hr ⊢
    nlinarith only [hr]
  have hj:1≤r.num.natAbs:=by have hh:=Int.natAbs_pos.mpr hnum.ne'; omega
  have hjk:2*r.num.natAbs<r.den := by
    rw [he] at hωπ
    have hh:2*Real.pi*r.num.natAbs<Real.pi*r.den:=(div_lt_iff₀ hkR).mp hωπ
    have hp:Real.pi*(2*(r.num.natAbs:ℝ))<Real.pi*r.den:=by nlinarith only [hh]
    exact_mod_cast (mul_lt_mul_iff_right₀ Real.pi_pos).mp hp
  exact ⟨r.num.natAbs,r.den,hj,hjk,r.reduced,he⟩

/-- A uniform pi/6 floor and the finite small-denominator tests exclude
all single harmonics, including irrational and unbounded-denominator ones. -/
theorem no_single_harmonic_of_finite_tests (Θ:Curve)
    (hfloor:∀ω:Levels.Frequency,0<(ω:ℝ)→Real.pi/6<Θ ω)
    (hsmall:∀j k:ℕ,1≤j→2*j<k→k≤5→∀ω:Levels.Frequency,
      (ω:ℝ)=2*Real.pi*j/k→Real.pi/k<Θ ω) :
    ∀ω:Levels.Frequency,¬ProgramSolution Θ nonzeroLags (Measure.dirac ω) := by
  intro ω hw
  obtain ⟨j,k,hj,hjk,hcop,hω⟩:=single_atom_rational hw
  have hk:2≤k:=by omega
  have ht:Θ ω≤Real.pi/k:=(Lattice.rational_atom_program_iff Θ hcop hk ω hω).mp hw
  by_cases hs:k≤5
  · exact (not_lt_of_ge ht) (hsmall j k hj hjk hs ω hω)
  · have hkR:(6:ℝ)≤k:=by exact_mod_cast (show 6≤k by omega)
    have hd:Real.pi/k≤Real.pi/6:=
      (div_le_div_iff₀ (by positivity : (0:ℝ)<k) (by norm_num : (0:ℝ)<6)).mpr
        (by nlinarith [Real.pi_pos])
    have hpos:0<(ω:ℝ):=by rw [hω]; positivity
    exact (not_lt_of_ge (ht.trans hd)) (hfloor ω hpos)

/-- Only four primitive interior frequencies survive these finite bounds
(k=3,4,5; j=1,1,1 or 2). The excluded endpoints were proved impossible above. -/
def SmallDenominatorChecks (Θ:Curve) : Prop:=
  ∀j:Fin 3,∀k:Fin 6,1≤j.val→2*j.val<k.val→∀ω:Levels.Frequency,
    (ω:ℝ)=2*Real.pi*j.val/k.val→Real.pi/k.val<Θ ω

theorem no_single_harmonic_of_small_checks (Θ:Curve)
    (hfloor:∀ω:Levels.Frequency,0<(ω:ℝ)→Real.pi/6<Θ ω)
    (hsmall:SmallDenominatorChecks Θ) :
    ∀ω:Levels.Frequency,¬ProgramSolution Θ nonzeroLags (Measure.dirac ω) := by
  apply no_single_harmonic_of_finite_tests Θ hfloor
  intro j k hj hjk hk ω hω
  have hj3:j<3:=by omega
  exact hsmall ⟨j,hj3⟩ ⟨k,by omega⟩ hj hjk ω hω

end polyak.Farey.Examples
