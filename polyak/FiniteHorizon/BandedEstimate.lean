import polyak.FiniteHorizon.KernelPlateau
import polyak.Growth.HorizonCertificate

/-!
Article: Appendix C, localization of a separated banded functional.
Use: arbitrary finite quadratic kernels and arbitrary zero-charge sampled-value
coefficients give the actual zero-price window energy bound. The inputs are the
source symbol and source pointwise interpolation combination, not an assumed
energy estimate or a factorization premise.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Filter Finset
open scoped BigOperators

def finiteValueCombination (S : Finset ℕ) (d : ℕ → ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n∈S,d n*h (k+n)

theorem sum_finiteValueCombination {S : Finset ℕ} {d h : ℕ → ℝ}
    (hcharge : ∑ n∈S,d n=0) (i j : ℕ) :
    (∑ k∈Icc i j,finiteValueCombination S d h k)=
      ∑ n∈S,d n*((∑ k∈Icc i j,h (k+n))-∑ k∈Icc i j,h k) := by
  unfold finiteValueCombination
  rw [sum_comm]
  simp_rw [←mul_sum,mul_sub]
  rw [sum_sub_distrib,←sum_mul,hcharge,zero_mul,sub_zero]

theorem abs_sum_finiteValueCombination_le {S : Finset ℕ} {d b h : ℕ → ℝ}
    (hcharge : ∑ n∈S,d n=0) (hb : ∀ k,0≤b k) {i j w : ℕ} (hij : i≤j)
    (hw : ∀ n∈S,n≤w) (hh : ∀ l,|h l|≤b l/2) :
    |∑ k∈Icc i j,finiteValueCombination S d h k|≤
      ((∑ n∈S,|d n|)/2)*(window b w i+window b w j) := by
  rw [sum_finiteValueCombination hcharge]
  calc
    _≤∑ n∈S,|d n*((∑ k∈Icc i j,h (k+n))-∑ k∈Icc i j,h k)|:=abs_sum_le_sum_abs _ _
    _≤∑ n∈S,|d n| *((window b w i+window b w j)/2):=by
      apply sum_le_sum
      intro n hn
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_interval_shift_difference_le hb hij (hw n hn) (fun l _ => hh l)) (abs_nonneg _)
    _=_:=by rw [←sum_mul]; ring

theorem finite_banded_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ) {ε : ℝ}
    (hε : 0<ε) (hneg : ∀ θ,kernelSymbol K θ≤ -ε) (hcharge : ∑ n∈S,d n=0)
    (N : ℕ) :
    ∃ C : ℝ,∃ w : ℕ,0<C ∧ N≤w ∧ ∀ (f : ℕ → E) (h : ℕ → ℝ),
      (∀ k,|h k|≤‖f k‖^2/2) →
      (∀ k,N≤k → 0≤kernelEval K (fun l => f l.toNat) k+finiteValueCombination S d h k) →
      ∀ i j,w ≤ i → i≤j → (∑ k∈Icc i j,‖f k‖^2)≤
        C*(window (fun k => ‖f k‖^2) w i+window (fun k => ‖f k‖^2) w j) := by
  obtain ⟨R,hR,hsupport⟩:=exists_kernel_radius K (max N (S.sup id))
  let w:=2*R
  let M:=kernelSize K+(∑ n∈S,|d n|)/2
  have hM : 0≤M:=add_nonneg (kernelSize_nonneg K) (by positivity)
  let C:=M/ε+1
  have hC : 0<C:=by dsimp [C]; linarith [div_nonneg hM hε.le]
  have hwN : N≤w:=by dsimp [w]; omega
  have hwS : ∀ n∈S,n≤w:=by
    intro n hn
    have hh : n≤S.sup id:=le_sup (f:=id) hn
    dsimp [w]
    omega
  refine ⟨C,w,hC,hwN,fun f h hh hnonneg i j hi hij => ?_⟩
  have hb : ∀ k,0≤‖f k‖^2:=fun k => sq_nonneg _
  have hquad:=sum_kernelEval_nat_interval_le K f hneg R hsupport i j hi hij
  have hvalues:=abs_sum_finiteValueCombination_le hcharge hb hij hwS hh
  have hsum : 0≤∑ k∈Icc i j,
      (kernelEval K (fun l => f l.toNat) k+finiteValueCombination S d h k):=by
    exact sum_nonneg (fun k hk => hnonneg k (by have := (mem_Icc.mp hk).1; omega))
  rw [sum_add_distrib] at hsum
  have hvalup:=(le_abs_self (∑ k∈Icc i j,finiteValueCombination S d h k)).trans hvalues
  have hnorm : ε*(∑ k∈Icc i j,‖f k‖^2)≤
      M*(window (fun k => ‖f k‖^2) w i+window (fun k => ‖f k‖^2) w j):=by
    dsimp [M,w] at *
    linarith
  have hwin : 0≤window (fun k => ‖f k‖^2) w i+window (fun k => ‖f k‖^2) w j:=
    add_nonneg (window_nonneg hb _ _) (window_nonneg hb _ _)
  have hdiv : (∑ k∈Icc i j,‖f k‖^2)≤
      (M/ε)*(window (fun k => ‖f k‖^2) w i+window (fun k => ‖f k‖^2) w j):=by
    calc
      _≤(M*(window (fun k => ‖f k‖^2) w i+window (fun k => ‖f k‖^2) w j))/ε:=
        (le_div_iff₀ hε).mpr (by nlinarith)
      _=_:=by ring
  dsimp [C]
  nlinarith

theorem kernelWindowEnergyBound_of_banded {A B β T ε : ℝ} {H : ℕ}
    (L : WindowPrice H) (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ)
    (hε : 0<ε) (hneg : ∀ θ,kernelSymbol K θ≤ -ε) (hcharge : ∑ n∈S,d n=0)
    (N : ℕ)
    (hsource : ∀ D : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin D)) A B β H,
      ZeroPriceRun L r → ∀ k,N≤k →
        0≤kernelEval K (discountedInteger r.x T) k+
          finiteValueCombination S d (discountedValue (sampleValue r) T) k) :
    ∃ C : ℝ,∃ w : ℕ,0<C ∧ KernelWindowEnergyBound A B β T C H w L := by
  -- The radius and scalar constant do not depend on the Hilbert dimension.
  let R:=max N (S.sup id)
  obtain ⟨radius,hradius,hsupport⟩:=exists_kernel_radius K R
  let width:=2*radius
  let M:=kernelSize K+(∑ n∈S,|d n|)/2
  let constant:=M/ε+1
  have hM : 0≤M:=add_nonneg (kernelSize_nonneg K) (by positivity)
  have hconstant : 0<constant:=by dsimp [constant]; linarith [div_nonneg hM hε.le]
  refine ⟨constant,width,hconstant,?_⟩
  intro D r hr i j hi hij
  let f:=discountedPosition r.x T
  let h:=discountedValue (sampleValue r) T
  let b:=discountedEnergy r.x T
  have hb : ∀ k,0≤b k:=discountedEnergy_nonneg r.x T
  have hf : (fun k => ‖f k‖^2)=b:=funext (norm_discountedPosition_sq r.x T)
  have hquad:=sum_kernelEval_nat_interval_le K f hneg radius hsupport i j hi hij
  rw [hf] at hquad
  have hwS : ∀ n∈S,n≤width:=by
    intro n hn
    have hh : n≤S.sup id:=le_sup (f:=id) hn
    dsimp [width,R] at *
    omega
  have hvalues:=abs_sum_finiteValueCombination_le hcharge hb hij hwS
    (fun k => r.abs_discountedValue_le T k)
  have hsum : 0≤∑ k∈Icc i j,
      (kernelEval K (discountedInteger r.x T) k+finiteValueCombination S d h k):=by
    apply sum_nonneg
    intro k hk
    apply hsource D r hr k
    have hk':=(mem_Icc.mp hk).1
    dsimp [width,R] at *
    omega
  rw [sum_add_distrib] at hsum
  have hkernel : (fun l : ℤ => f l.toNat)=discountedInteger r.x T:=rfl
  rw [hkernel] at hquad
  have hvalup:=(le_abs_self (∑ k∈Icc i j,finiteValueCombination S d h k)).trans hvalues
  have hnorm : ε*(∑ k∈Icc i j,b k)≤M*(window b width i+window b width j):=by
    dsimp [M]
    change |∑ k∈Icc i j,finiteValueCombination S d h k|≤_ at hvalues
    linarith
  have hwin : 0≤window b width i+window b width j:=
    add_nonneg (window_nonneg hb _ _) (window_nonneg hb _ _)
  have hdiv : (∑ k∈Icc i j,b k)≤(M/ε)*(window b width i+window b width j):=by
    calc
      _≤(M*(window b width i+window b width j))/ε:=
        (le_div_iff₀ hε).mpr (by nlinarith)
      _=_:=by ring
  have hfinal : (∑ k∈Icc i j,b k)≤constant*(window b width i+window b width j):=by
    dsimp [constant]
    nlinarith
  simpa only [mass,Ico_add_one_right_eq_Icc,←window_eq_energyWindow] using hfinal

end polyak.FiniteHorizon
