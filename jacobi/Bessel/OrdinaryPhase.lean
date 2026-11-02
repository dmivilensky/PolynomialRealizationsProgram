import jacobi.Bessel.RestoringState
import jacobi.Bessel.WeylPhase
import jacobi.Oscillation.PhaseZeros

/-!
Article: jacobi, Proposition B.1.
The ordinary Pruefer phase of the original Bessel wave is constructed by
the genuine state integral. Its inverse-square equation and exact phase
increments at the actual canonical zeros are proved. This phase is used
instead of assuming the classical J/Y phase estimates of B1.
Use: its exact zero increments and literal inverse-square derivative yield the cubic McMahon remainder.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine ordinary Pruefer phase increment of the original Bessel wave.
Use: its exact zero increments and literal inverse-square derivative yield the cubic McMahon remainder.
Article: jacobi, Proposition B.1.
-/
def ordinaryPhase (a : ℝ) (ha : -1<a) (base x : ℝ) : ℝ := (restoringState a ha).phase base x

/-- Every actual positive Bessel zero is a genuine zero of the original Liouville wave.
Use: all phase bases and nodal endpoints used in McMahon are true zeros of the original source function.
Article: jacobi, Proposition B.1.
Proof: the already proved cylindrical source zero and exact normalized entire-function identification imply the original wave zero. -/
theorem wave_positiveZero_zero {a : ℝ} (ha : -1<a) (k : ℕ) : wave a (positiveZero a ha k)=0 := by
  rw [wave_zero_iff a (positiveZero_properties ha k).1]
  exact (cylindrical_zero_iff ha (positiveZero_properties ha k).1).mp (positiveZero_is_zero ha k)

/-- The actual original Bessel wave has no zero between any consecutive original positive Bessel zeros.
Use: fixes exact genuine phase increments without borrowing an asymptotic numbering theorem.
Article: jacobi, Proposition B.1.
Proof: specialize the proved actual scaled zero-free interval to frequency one. -/
theorem wave_no_zero_between {a x : ℝ} (ha : -1<a) (k : ℕ)
    (hx : x∈Ioo (positiveZero a ha k) (positiveZero a ha (k+1))) : wave a x≠0 := by
  simpa only [scaledZero,div_one,scaledWave,one_mul,Real.one_rpow,inv_one] using
    scaledWave_no_zero_between ha (show (0:ℝ)<1 by norm_num) k
      (by simpa only [scaledZero,div_one] using hx)

/-- The actual original Bessel phase speed is at least one half beyond the explicit restoring threshold.
Use: proves strict phase monotonicity on every large-zero interval in McMahon's remainder argument.
Article: jacobi, Proposition B.1.
Proof: the original restoring coefficient has its proved one-half lower
bound; the exact original normalized-state speed preserves that bound. -/
theorem ordinaryPhase_density_lower {a x : ℝ} (ha : -1<a) (hx : 2*(a^2+1)≤x) :
    (1/2:ℝ)≤(restoringState a ha).phaseDensity x := by
  have hp : 0<x := by nlinarith [sq_nonneg a]
  exact (restoringState a ha).phaseDensity_lower hp (by norm_num) (wave_restoring_bound a hx)

/-- A genuine zero-based ordinary Bessel phase obeys the exact actual inverse-square phase equation.
Use: its actual oscillatory remainder determines the original cubic McMahon correction.
Article: jacobi, Proposition B.1.
Proof: the phase integral has its true ordinary derivative. The actual
base zero and proved rotating-state representation identify the normalized
value square with the literal sine square of this original phase. -/
theorem ordinaryPhase_hasDerivAt {a base x : ℝ} (ha : -1<a) (hb : 0<base) (hx : 0<x)
    (hz : wave a base=0) :
    HasDerivAt (ordinaryPhase a ha base)
      (1+(1/4-a^2)/x^2*sin (ordinaryPhase a ha base x)^2) x := by
  have h := (restoringState a ha).phase_hasDerivAt (convex_Ioi 0) hb hx
  have he := (restoringState a ha).phaseDensity_at_zero isOpen_Ioi (convex_Ioi 0) hb hx hz
  change (restoringState a ha).phaseDensity x=
    1+((1+(1/4-a^2)/x^2)-1)*sin (ordinaryPhase a ha base x)^2 at he
  rw [he] at h
  change HasDerivAt ((restoringState a ha).phase base)
    (1+(1/4-a^2)/x^2*sin ((restoringState a ha).phase base x)^2) x
  simpa only [ordinaryPhase,add_sub_cancel_left] using h

/-- The genuinely constructed ordinary Bessel phase advances by exactly pi per actual canonical zero after the explicit restoring threshold.
Use: fixes the exact indexed phase constants in the finite-interval proof of McMahon's expansion and its cubic remainder.
Article: jacobi, Proposition B.1.
Proof: the true base is an actual Bessel zero. Every later original nodal
interval is zero-free and has actual phase speed at least one half.
The proved general phase increment theorem therefore gives exactly pi
per interval; induction sums those genuine increments. -/
theorem ordinaryPhase_numbered_zero {a : ℝ} (ha : -1<a) (k : ℕ)
    (hk : 2*(a^2+1)≤positiveZero a ha k) (m : ℕ) :
    ordinaryPhase a ha (positiveZero a ha k) (positiveZero a ha (k+m))=(m:ℝ)*Real.pi := by
  -- Every zero and every zero-free interval here comes from the original exhaustive Bessel enumeration.
  let S := restoringState a ha
  have hbase := (positiveZero_properties ha k).1
  have hzero := wave_positiveZero_zero ha k
  induction m with
  | zero => simp only [Nat.add_zero,ordinaryPhase,RestoringSolution.phase_self,Nat.cast_zero,zero_mul]
  | succ m ih =>
    have hstep := S.phase_increment_between_zeros isOpen_Ioi (convex_Ioi 0) hbase hzero
      (positiveZero_properties ha (k+m)).1 (positiveZero_properties ha (k+m+1)).1
      (positiveZero_strictMono ha (Nat.lt_succ_self (k+m)))
      (wave_positiveZero_zero ha (k+m)) (wave_positiveZero_zero ha (k+m+1))
      (fun x hx => wave_no_zero_between ha (k+m) hx) (by
        intro x hx
        have hstart := ((positiveZero_strictMono ha).monotone (Nat.le_add_right k m)).trans hx.1
        exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (ordinaryPhase_density_lower ha (hk.trans hstart)))
    change ordinaryPhase a ha (positiveZero a ha k) (positiveZero a ha (k+m+1))-
      ordinaryPhase a ha (positiveZero a ha k) (positiveZero a ha (k+m))=Real.pi at hstep
    rw [ih] at hstep
    rw [show k+(m+1)=k+m+1 by omega]
    push_cast
    linarith

end
end jacobi.Bessel
