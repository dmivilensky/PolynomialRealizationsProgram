import krylov.LinearAlgebra.RiccatiBarrier
import krylov.LinearAlgebra.RiccatiError
import krylov.LinearAlgebra.ShiftedPivotGap
import krylov.LinearAlgebra.VanishingContraction
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine Nevai positive-pivot asymptotic stability.
Use: derive the actual stable Jacobi pivot limit from true limiting diagonal and edge data and genuine positive original and shifted pivots.
Source: exact actual LDL Riccati recurrences, the proved shifted-pivot gap and positive lower barrier, and genuine vanishing-forcing contraction.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter
open scoped Topology

/-- The genuine bounded original Jacobi pivots converge to the true stable positive fixed pivot when the actual shifted pivots remain positive and the original Jacobi coefficients have their stated limits.
Use: The genuine bounded original Jacobi pivots converge to the true stable positive fixed pivot when the actual shifted pivots remain positive and the original Jacobi coefficients have their stated limits.
Article: main_krylov, prop:phi(c), genuine Nevai positive-pivot asymptotic stability.
Proof: Use actual shifted-pivot positivity to exclude the unstable branch; the genuine original pivot error then has a strict eventual contraction with true vanishing coefficient defects. -/
theorem positive_pivot_limit (d s A B : ℕ → ℝ) (mu L a b D : ℝ)
    (hmu : 0 < mu) (hb : 0 < b) (hD : b<D) (hfixed : a=D+b^2/D) (hshift : a-mu=2*b)
    (hd : ∀ n,0 < d n) (hs : ∀ n,0 < s n) (hzero : d 0=mu+s 0) (hcap : ∀ n,d n≤L)
    (hdrec : ∀ n,d (n+1)=A (n+1)-(B n)^2/d n)
    (hsrec : ∀ n,s (n+1)=A (n+1)-mu-(B n)^2/s n)
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b)) :
    Tendsto d atTop (𝓝 D) := by
  -- Select a genuine sub-edge shifted-pivot barrier strictly above the actual unstable fixed-pivot ratio.
  have hDpos : 0 < D := hb.trans hD
  let dm := b^2/D
  have hdm : 0≤dm := by dsimp only [dm];positivity
  have hdmb : dm<b := by
    dsimp only [dm]
    apply (div_lt_iff₀ hDpos).mpr
    nlinarith [mul_pos hb (sub_pos.mpr hD)]
  let c := (b+dm)/2
  have hc : 0 < c := by dsimp only [c];positivity
  have hcb : c<b := by dsimp only [c];linarith
  have hdmc : dm<c := by dsimp only [c];linarith
  -- The original and genuinely shifted LDL recurrences force the true positive shift gap.
  have hgap := positive_shifted_pivot_gap d s A B mu hmu.le hs hzero hdrec hsrec
  have hAsh : Tendsto (fun n => A n-mu) atTop (𝓝 (2*b)) := by
    rw [← hshift]
    exact hA.sub_const mu
  have hsbar := positive_riccati_eventual_lower s (fun n => A n-mu) B b hs hsrec hAsh hB c hc hcb
  have hdbar : ∀ᶠ n in atTop,mu+c≤d n := by
    filter_upwards [hsbar] with n hn
    linarith [hgap n]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hdbar
  let r := dm/(mu+c)
  have hr : 0≤r := by dsimp only [r];positivity
  have hr1 : r<1 := (div_lt_one (by positivity : 0 < mu+c)).mpr (by linarith)
  -- Only the actual original coefficient defects drive the genuine stable-pivot error recurrence.
  let e := fun n => |d n-D|
  let f := fun n => |A (n+1)-a|+|(B n)^2-b^2|/mu
  have he (n : ℕ) : 0≤e n := abs_nonneg _
  have hecap (n : ℕ) : e n≤L+D := by
    dsimp only [e]
    rw [abs_le]
    constructor <;> linarith [hd n,hcap n]
  have hf : Tendsto f atTop (𝓝 0) := by
    have ht := ((hA.comp (tendsto_add_atTop_nat 1)).sub_const a).abs.add
      (((hB.pow 2).sub_const (b^2)).abs.div_const mu)
    simpa only [f,Function.comp_apply,sub_self,abs_zero,zero_div,add_zero] using ht
  -- The genuine lower barrier supplies the actual strict contraction coefficient before the original error limit is concluded.
  have hconv : Tendsto e atTop (𝓝 0) := bounded_vanishing_contraction e f (L+D) r he hecap hr hr1 hf N (by
    intro n hn
    have hcoef : b^2/(D*d n)≤r := by
      rw [div_mul_eq_div_div]
      exact div_le_div_of_nonneg_left hdm (by positivity) (hN n hn)
    have hmn : mu≤d n := by linarith [hgap n,hs n]
    dsimp only [e,f]
    rw [hdrec]
    have ht := positive_riccati_error_bound (A (n+1)) (B n) b D (d n) mu r hDpos hmu hmn hcoef
    simpa only [← hfixed,add_assoc] using ht)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hconv
end
end krylov.LinearAlgebra
