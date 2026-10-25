import polyak.CertifiedExamples.Plateaus.Primal
import polyak.CertifiedExamples.Plateaus.SymbolTransfer

/-! Finite polynomial primary data are transported to the original regular
program. In particular, primal masses are divided by the genuine phase factor;
matrix rank and every source constraint survive that change of coordinates. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking
open scoped BigOperators

def sourceLagMatrix {d : ℕ} (q : Tuning) (n : Fin d  →  ℤ) (u : Fin d  →  Frequency) :
    Matrix (Fin d) (Fin d) ℝ := fun r i =>
  Farey.Certificates.signedLagPolynomial q (n r) (Real.cos (u i:ℝ))

structure PolynomialPrimaryData (q : Tuning) (L d : ℕ) where
  period_ge : 3≤L
  dimension_pos : 0<d
  atoms : Fin d  →  Frequency
  atoms_injective : Function.Injective atoms
  atoms_grid : ∀i,atoms i∈periodicGrid L
  atoms_lt_pi : ∀i,(atoms i:ℝ)<Real.pi
  reps : Fin d  →  ℤ
  reps_pos : ∀i,0<reps i
  reps_lt : ∀i,reps i<L
  reps_injective : Function.Injective reps
  baseLag : Fin d  →  ℤ
  base_nonzero : ∀i,baseLag i≠0
  base_mod : ∀i,baseLag i%(L:ℤ)=reps i
  rho : Fin d  →  ℝ
  rho_pos : ∀i,0<rho i
  kernel : ∀r,(∑i,rho i*sourceLagMatrix q baseLag atoms r i)=0
  inactive : ∀ r : ℤ,0<r → r<L → (∀i,r≠reps i) → 
    0<∑i,rho i*Farey.Certificates.signedLagPolynomial q r (Real.cos (atoms i:ℝ))
  minimizer : 0<∑i,rho i*q.Xi (Real.cos (atoms i:ℝ))
  rank : (sourceLagMatrix q baseLag atoms).rank=d-1
  lags : Finset ℤ
  lags_nonzero : ∀n∈lags,n≠0
  classes : ∀n∈lags,n%(L:ℤ)=0 ∨ ∃i,n%(L:ℤ)=reps i
  dual : ℤ → ℝ
  dual_pos : ∀n∈lags,0<dual n
  dual_sum : ∑n∈lags,dual n=1
  lag_one : 1∈lags
  class_pair : ∀i,∃n₁∈lags,∃n₂∈lags,n₁≠n₂ ∧
    n₁%(L:ℤ)=reps i ∧ n₂%(L:ℤ)=reps i
  pinning_det : Matrix.det (fun i r : Fin d => Real.sin ((reps r:ℝ)*(atoms i:ℝ)-
    tuningCurve q (atoms i)))≠0

namespace PolynomialPrimaryData
variable {q : Tuning} {L d : ℕ} (P : PolynomialPrimaryData q L d)

theorem atoms_interior (i : Fin d) : 0<(P.atoms i:ℝ) ∧ (P.atoms i:ℝ)<Real.pi :=
  ⟨(P.atoms_grid i).1,P.atoms_lt_pi i⟩

theorem lag_rep_eq_base (r i : Fin d) :
    (tuningCurve q).lag (P.reps r) (P.atoms i)=
      (tuningCurve q).lag (P.baseLag r) (P.atoms i) := by
  rw [lag_mod_grid _ (P.atoms_grid i) (P.baseLag r),P.base_mod r]

def primal (i : Fin d) : NNReal := Real.toNNReal (actualPrimal q P.atoms P.rho i)

theorem coe_primal (i : Fin d) : (P.primal i:ℝ)=actualPrimal q P.atoms P.rho i :=
  Real.coe_toNNReal _ (actualPrimal_pos P.dimension_pos q P.atoms P.rho P.atoms_interior P.rho_pos i).le

theorem primal_positive (i : Fin d) : 0<P.primal i := by
  have hp : (0:ℝ)<(P.primal i:ℝ) := by
    rw [P.coe_primal]
    exact actualPrimal_pos P.dimension_pos q P.atoms P.rho P.atoms_interior P.rho_pos i
  exact_mod_cast hp

theorem primal_normalized : (∑i,P.primal i)=1 := by
  apply NNReal.coe_injective
  push_cast
  simp only [P.coe_primal]
  exact actualPrimal_sum P.dimension_pos q P.atoms P.rho P.atoms_interior P.rho_pos

theorem original_tight (r : Fin d) :
    (∑i,(P.primal i:ℝ)*(tuningCurve q).lag (P.reps r) (P.atoms i))=0 := by
  simp only [P.coe_primal,P.lag_rep_eq_base]
  rw [actualPrimal_lag q P.atoms P.rho P.atoms_interior (P.baseLag r) (P.base_nonzero r)]
  change (∑i,P.rho i*sourceLagMatrix q P.baseLag P.atoms r i)/_=0
  rw [P.kernel,zero_div]

theorem original_inactive {r : ℤ} (hr : 0<r) (hL : r<L) (hne : ∀i,r≠P.reps i) :
    0<∑i,(P.primal i:ℝ)*(tuningCurve q).lag r (P.atoms i) := by
  simp only [P.coe_primal]
  rw [actualPrimal_lag q P.atoms P.rho P.atoms_interior r hr.ne']
  exact div_pos (P.inactive r hr hL hne)
    (primal_total_pos P.dimension_pos q P.atoms P.rho P.atoms_interior P.rho_pos)

theorem original_minimizer :
    0<∑i,(P.primal i:ℝ)*(tuningCurve q).minimizer (P.atoms i) := by
  simp only [P.coe_primal]
  rw [actualPrimal_minimizer q P.atoms P.rho P.atoms_interior]
  exact div_pos P.minimizer
    (primal_total_pos P.dimension_pos q P.atoms P.rho P.atoms_interior P.rho_pos)

theorem original_rank :
    Matrix.rank (fun r i : Fin d => (tuningCurve q).lag (P.reps r) (P.atoms i))=d-1 := by
  classical
  let D := Matrix.diagonal (fun i=>phaseFactor q (P.atoms i))
  have hD : D.det≠0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>(phaseFactor_pos q (P.atoms i) (P.atoms_interior i)).ne')
  have he : (fun r i : Fin d => (tuningCurve q).lag (P.reps r) (P.atoms i))=
      sourceLagMatrix q P.baseLag P.atoms*D := by
    ext r i
    rw [Matrix.mul_diagonal,P.lag_rep_eq_base]
    rw [Farey.Certificates.lag_polynomial_factor q (P.baseLag r) (P.base_nonzero r)
      (P.atoms i) (P.atoms_interior i)]
    change phaseFactor q (P.atoms i)*_= _*phaseFactor q (P.atoms i)
    simp only [sourceLagMatrix]
    ring
  rw [he,Matrix.rank_mul_eq_left_of_det_ne_zero D _ hD]
  exact P.rank

theorem pinning_positive (i : Fin d) : 0<pinningPolynomial P.lags P.dual (P.atoms i) := by
  unfold pinningPolynomial
  apply Finset.sum_pos'
  · intro n hn
    exact mul_nonneg (P.dual_pos n hn).le (sub_nonneg.mpr (Real.cos_le_one _))
  · refine ⟨1,P.lag_one,?_⟩
    simp only [Int.cast_one,one_mul]
    apply mul_pos (P.dual_pos 1 P.lag_one)
    have hc := Real.strictAntiOn_cos (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (P.atoms i).property (P.atoms_interior i).1
    simpa only [Real.cos_zero] using sub_pos.mpr hc

def regularData
    (hzero : ∀i,polynomialSymbol q P.lags P.dual (Real.cos (P.atoms i:ℝ))=0)
    (hslope : ∀i,deriv (polynomialSymbol q P.lags P.dual) (Real.cos (P.atoms i:ℝ))=0)
    (hcurv : ∀i,deriv^[2] (polynomialSymbol q P.lags P.dual) (Real.cos (P.atoms i:ℝ))<0)
    (hstrict : ∀c∈Set.Icc (-1:ℝ) 1,(∀i,c≠Real.cos (P.atoms i:ℝ)) → 
      polynomialSymbol q P.lags P.dual c<0) : RegularData q 0 L where
  period_ge := P.period_ge
  d := d
  atoms := P.atoms
  atoms_injective := P.atoms_injective
  atoms_grid := P.atoms_grid
  atoms_lt_pi := P.atoms_lt_pi
  reps := P.reps
  reps_pos := P.reps_pos
  reps_lt := P.reps_lt
  reps_injective := P.reps_injective
  lags := P.lags
  lags_nonzero := P.lags_nonzero
  classes := P.classes
  primal := P.primal
  primal_pos := P.primal_positive
  primal_sum := P.primal_normalized
  dual := P.dual
  dual_pos := P.dual_pos
  dual_sum := P.dual_sum
  tight := by simpa only [Geometry.shiftedCurve_zero] using P.original_tight
  inactive := by
    intro r hr hL hne
    simpa only [Geometry.shiftedCurve_zero] using P.original_inactive hr hL hne
  minimizer_strict := by simpa only [Geometry.shiftedCurve_zero] using P.original_minimizer
  rank := by simpa only [Geometry.shiftedCurve_zero] using P.original_rank
  dual_strict := by
    classical
    intro x hx hxπ haway
    refine full_symbol_strict q P.lags P.dual P.lags_nonzero
      (fun n hn=>(P.dual_pos n hn).le) P.lag_one (P.dual_pos 1 P.lag_one)
      (Finset.univ.image P.atoms) ?_ ⟨hx,hxπ⟩ ?_
    · intro c hc hne
      apply hstrict c hc
      intro i he
      exact hne (P.atoms i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) he
    · intro ω hω
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hω
      exact haway i
  support_curvature := fun i=>support_curvature_of_polynomial q P.lags P.dual
    P.lags_nonzero (P.atoms i) (P.atoms_interior i) (hzero i) (hslope i) (hcurv i)
  endpoint_curvature := by
    apply endpoint_moment_of_polynomial q P.lags P.dual P.lags_nonzero
    apply hstrict 1 (by constructor <;> norm_num)
    intro i he
    have hi := (P.atoms_interior i).1
    have hc : Real.cos (0:ℝ)=Real.cos (P.atoms i:ℝ) := by simpa only [Real.cos_zero] using he
    have hh := Real.strictAntiOn_cos.injOn
      (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) (P.atoms i).property hc
    linarith
  pinning_pos := P.pinning_positive
  class_pair := P.class_pair
  pinning_det := by simpa only [Geometry.shiftedCurve_zero] using P.pinning_det

end PolynomialPrimaryData
end polyak.CertifiedExamples.Plateaus
