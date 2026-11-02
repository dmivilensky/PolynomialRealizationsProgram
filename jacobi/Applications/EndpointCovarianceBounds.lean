import jacobi.Applications.EndpointCovariance
import jacobi.Applications.EndpointParticular

/-!
Article: jacobi, Theorem 5.1.
The actual impulse covariances differ from explicit particular polynomials
by bounded, linear and quadratic errors. This argument treats every b>-1
at once and uses only finite sums and exact rational contraction.
Use: EndpointLimit proves the original endpoint-gain asymptotic.
-/
namespace jacobi.Applications
noncomputable section
set_option maxHeartbeats 2000000

/-- The three genuine original covariances have uniformly controlled errors of their exact successive polynomial orders.
Use: endpoint_gain_limit divides the true squared endpoint gain's quadratic error by k^3.
Article: jacobi, Lemma A.2.
Proof: the momentum contracts the difference variance sufficiently to absorb the exact inverse-square defect. The other two actual error recurrences then sum a constant into a linear bound and a linear bound into a quadratic bound. This includes b=0 without a separate logarithmic estimate. -/
theorem endpointCovariance_bounds {b:ℝ} (hb:-1<b) :
    ∃ M:ℝ,0<M ∧ ∀ k:ℕ,1≤k →
      |endpointDifference b k-endpointDPoly b k|≤M ∧
      |endpointCross b k-endpointCPoly b k|≤M*k ∧
      |endpointEnergy b k-endpointEPoly b k|≤M*(k:ℝ)^2 := by
  -- One sufficiently large constant absorbs the genuine initial errors and all future variance forcing.
  have hb1:0<b+1:=by linarith
  have ha:0<2*b+3:=by linarith
  have hK:0≤endpointK b:=by unfold endpointK; positivity
  let M := |endpointDifference b 1-endpointDPoly b 1|+
    |endpointCross b 1-endpointCPoly b 1|+|endpointEnergy b 1-endpointEPoly b 1|+
    endpointK b/(b+1)^2+1
  have hforce:0≤endpointK b/(b+1)^2:=div_nonneg hK (sq_nonneg _)
  have hM:0<M:=by dsimp [M]; positivity
  have hM0:=hM.le
  have hKM:endpointK b≤M*(b+1)^2:=by
    apply (div_le_iff₀ (sq_pos_of_pos hb1)).mp
    dsimp [M]
    linarith [abs_nonneg (endpointDifference b 1-endpointDPoly b 1),
      abs_nonneg (endpointCross b 1-endpointCPoly b 1),
      abs_nonneg (endpointEnergy b 1-endpointEPoly b 1)]
  refine ⟨M,hM,?_⟩
  intro k hk
  induction k,hk using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one,mul_one,one_pow]
    dsimp [M]
    constructor
    · linarith [abs_nonneg (endpointCross b 1-endpointCPoly b 1),
        abs_nonneg (endpointEnergy b 1-endpointEPoly b 1)]
    constructor
    · linarith [abs_nonneg (endpointDifference b 1-endpointDPoly b 1),
        abs_nonneg (endpointEnergy b 1-endpointEPoly b 1)]
    · linarith [abs_nonneg (endpointDifference b 1-endpointDPoly b 1),
        abs_nonneg (endpointCross b 1-endpointCPoly b 1)]
  | succ k hk ih =>
    have hkp:0<k:=by omega
    have hkn:(1:ℝ)≤k:=by exact_mod_cast hk
    obtain ⟨hbeta0,hbeta1⟩:=nesterovMomentum_bounds hb hk
    have hden:=nesterov_denominator_pos hb hkp
    have hgap:(b+1)^2≤((k:ℝ)+b)^2-((k:ℝ)-1)^2:=by
      nlinarith [mul_nonneg hb1.le (sub_nonneg.mpr hkn)]
    have hcontract:(nesterovMomentum b k)^2*M+endpointK b/((k:ℝ)+b)^2≤M:=by
      have he:(nesterovMomentum b k)^2*M+endpointK b/((k:ℝ)+b)^2=
          (((k:ℝ)-1)^2*M+endpointK b)/((k:ℝ)+b)^2:=by
        simp only [nesterovMomentum,ite_eq_right (Nat.ne_of_gt hkp)]
        field_simp

      rw [he]
      apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hgap hM0]
    have hd: endpointDifference b (k+1)-endpointDPoly b (k+1)=
        (nesterovMomentum b k)^2*(endpointDifference b k-endpointDPoly b k)+
          endpointK b/((k:ℝ)+b)^2:=by
      rw [endpointDifference_recurrence,endpointDPoly_recurrence hb hk]
      ring
    have hdb:|endpointDifference b (k+1)-endpointDPoly b (k+1)|≤M:=by
      rw [hd]
      exact (abs_add_le _ _).trans ((add_le_add
        (by rw [abs_mul,abs_of_nonneg (sq_nonneg _)];
            exact mul_le_mul_of_nonneg_left ih.1 (sq_nonneg _))
        (le_of_eq (abs_of_nonneg (div_nonneg hK (sq_nonneg _))))).trans hcontract)
    have hc:endpointCross b (k+1)-endpointCPoly b (k+1)=
        nesterovMomentum b k*(endpointCross b k-endpointCPoly b k)+
          (endpointDifference b (k+1)-endpointDPoly b (k+1)):=by
      rw [endpointCross_recurrence,endpointCPoly_recurrence hb hk]
      ring
    have hcb:|endpointCross b (k+1)-endpointCPoly b (k+1)|≤M*(k+1:ℕ):=by
      rw [hc]
      calc
        _≤nesterovMomentum b k*(M*k)+M := (abs_add_le _ _).trans
          (add_le_add (by
            rw [abs_mul,abs_of_nonneg hbeta0]
            exact mul_le_mul_of_nonneg_left ih.2.1 hbeta0) hdb)
        _≤1*(M*k)+M:=add_le_add
          (mul_le_mul_of_nonneg_right hbeta1 (mul_nonneg hM0 (Nat.cast_nonneg _))) le_rfl
        _=M*(k+1:ℕ):=by push_cast; ring
    have he:endpointEnergy b (k+1)-endpointEPoly b (k+1)=
        (endpointEnergy b k-endpointEPoly b k)+
        2*nesterovMomentum b k*(endpointCross b k-endpointCPoly b k)+
          (endpointDifference b (k+1)-endpointDPoly b (k+1)):=by
      rw [endpointEnergy_recurrence,endpointEPoly_recurrence hb hk]
      ring
    refine ⟨by simpa only [Nat.cast_add,Nat.cast_one] using hdb,by simpa only [Nat.cast_add,Nat.cast_one] using hcb,?_⟩
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    calc
      _≤(|endpointEnergy b k-endpointEPoly b k|+
          |2*nesterovMomentum b k*(endpointCross b k-endpointCPoly b k)|)+
          |endpointDifference b (k+1)-endpointDPoly b (k+1)|:=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _≤M*(k:ℝ)^2+2*nesterovMomentum b k*(M*k)+M:=by
        apply add_le_add _ hdb
        apply add_le_add ih.2.2
        rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hbeta0)]
        exact mul_le_mul_of_nonneg_left ih.2.1 (mul_nonneg (by norm_num) hbeta0)
      _≤M*(k:ℝ)^2+2*(M*k)+M:=by
        nlinarith [mul_le_mul_of_nonneg_right hbeta1 (mul_nonneg hM0 (Nat.cast_nonneg k))]
      _=M*((k:ℝ)+1)^2:=by ring

end
end jacobi.Applications
