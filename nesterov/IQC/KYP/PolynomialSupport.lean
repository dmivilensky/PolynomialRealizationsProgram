import nesterov.IQC.StationaryFilters
import nesterov.IQC.KYP.StrictStorage
import polyak.Energy.CombinationSupport

/-! The actual polynomial certificate has exactly the finite width D+M. -/
namespace nesterov.IQC.KYP
noncomputable section
open polyak.General.IQC polyak.Energy

/-- Retain every coefficient while changing nonnegative integer shifts to naturals. -/
def ofKernel (K : Kernel) : NatKernel:=K.map (fun p=>(p.1,(p.2.1.toNat,p.2.2.toNat)))

theorem ofKernel_toKernel {K : Kernel} {N : ℕ} (hK : KernelSupported 0 N K) :
    (ofKernel K).toKernel=K := by
  unfold ofKernel NatKernel.toKernel
  rw [List.map_map]
  calc
    _=List.map id K:=by
      apply List.map_congr_left
      intro p hp
      have h:=hK p hp
      simp only [Function.comp_apply,Int.toNat_of_nonneg h.1.1,Int.toNat_of_nonneg h.2.1,id_eq]
    _=K:=List.map_id K

theorem ofKernel_supported {K : Kernel} {N : ℕ} (hK : KernelSupported 0 N K) :
    (ofKernel K).Supported N := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  have hh:=hK q hq
  change q.2.1.toNat≤N ∧ q.2.2.toNat≤N
  exact ⟨Int.toNat_le.mpr (by omega),Int.toNat_le.mpr (by omega)⟩

end
end nesterov.IQC.KYP

namespace nesterov.IQC
noncomputable section
open polyak.General.IQC polyak.Energy

/-- Ascending polynomial coefficients are supported in the stated finite window. -/
theorem coefficientFilter_supported {d D : ℕ} (v : Fin d→ℝ) (hd : d≤D+1) :
    FilterSupported 0 D (coefficientFilter v) := by
  intro p hp
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp
  change (0:ℤ)≤j.val ∧ (j.val:ℤ)≤D
  exact ⟨by omega,by have :=j.isLt; omega⟩

theorem twoFilterKernel_supported {a : nesterov.Spectral.SymbolPair} {t : ℝ}
    (cert : nesterov.Duality.StrictCertificate a t) {D M : ℕ} {X S : LinearFilter}
    (hX : FilterSupported 0 D X) (hS : FilterSupported 0 D S)
    (hM : ∀ n∈cert.lags,n≤M) :
    KernelSupported 0 (D+M) (twoFilterKernel X S cert) := by
  have hX':=hX.weaken (by omega : (0:ℤ)≤0) (by omega : (D:ℤ)≤D+M)
  have hS':=hS.weaken (by omega : (0:ℤ)≤0) (by omega : (D:ℤ)≤D+M)
  have hlag (n : ℕ) (hn : n∈cert.lags) :
      KernelSupported 0 (D+M)
        (kernelScale (2*Real.exp (-(n*t)))
          (kernelScale (cert.α n) (pairKernel 1 X
            (filterScale (Real.exp (n*t)) (filterShift n X)) S
            (filterScale (Real.exp (n*t)) (filterShift n S)))++
          kernelScale (cert.β n) (pairKernel (-1) X
            (filterScale (Real.exp (n*t)) (filterShift n X)) S
            (filterScale (Real.exp (n*t)) (filterShift n S))))) := by
    have hm:=hM n hn
    have hY:=((hX.shift n).weaken (by omega : (0:ℤ)≤0+n)
      (by omega : (D:ℤ)+n≤D+M)).scale (Real.exp (n*t))
    have hT:=((hS.shift n).weaken (by omega : (0:ℤ)≤0+n)
      (by omega : (D:ℤ)+n≤D+M)).scale (Real.exp (n*t))
    exact (((pairKernel_supported hX' hY hS' hT 1).scale _).append
      ((pairKernel_supported hX' hY hS' hT (-1)).scale _)).scale _
  exact ((KernelSupported.flatMap (fun n hn=>hlag n (Finset.mem_toList.mp hn))).append
    ((starKernel_supported hX' hS' 1).scale _)).append ((starKernel_supported hX' hS' (-1)).scale _)

end
end nesterov.IQC
