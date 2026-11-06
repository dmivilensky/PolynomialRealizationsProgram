import nesterov.IQC.KYP.Storage

/-! Strict finite-state dissipation obtained by adding a small full-window energy. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.Energy

/-- Full window energy, including the incoming coordinate. -/
def diagonalKernel (N : ℕ) (η : ℝ) : NatKernel:=
  List.ofFn (fun j : Fin (N+1)=>(η,(j.val,j.val)))

theorem diagonalKernel_supported (N : ℕ) (η : ℝ) : (diagonalKernel N η).Supported N := by
  intro p hp
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp
  change j.val≤N ∧ j.val≤N
  have h:=j.isLt
  exact ⟨by omega,by omega⟩

theorem diagonalKernel_symbol (N : ℕ) (η : ℝ) (θ : FrequencyCircle) :
    kernelSymbol (diagonalKernel N η).toKernel θ=η*(N+1) := by
  simp [diagonalKernel,NatKernel.toKernel,kernelSymbol,character,List.sum_ofFn]
  ring

theorem NatKernel.supported_append {N : ℕ} {K L : NatKernel}
    (hK : K.Supported N) (hL : L.Supported N) : (K++L).Supported N := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hK p) (hL p)

theorem NatKernel.toKernel_append (K L : NatKernel) :
    (K++L).toKernel=K.toKernel++L.toKernel:=by simp [NatKernel.toKernel]

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem instantaneous_append {N : ℕ} (K L : NatKernel) (x : Fin N→E) (d : E) :
    instantaneous (K++L) x d=instantaneous K x d+instantaneous L x d := by
  simp [instantaneous,NatKernel.eval]

theorem instantaneous_diagonal {N : ℕ} (η : ℝ) (x : Fin N→E) (d : E) :
    instantaneous (diagonalKernel N η) x d=η*((∑ j : Fin N,‖x j‖^2)+‖d‖^2) := by
  simp only [instantaneous,NatKernel.eval,diagonalKernel,List.map_ofFn,List.sum_ofFn,
    Nat.zero_add]
  simp only [Function.comp_def,real_inner_self_eq_norm_sq]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.lt_irrefl,↓reduceDIte]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [j.isLt,↓reduceDIte]

variable [CompleteSpace E]

/-- The needed strict KYP theorem. It produces an actual bounded symmetric
quadratic storage on the fixed state and a strictly positive dissipation.
Its proof uses the exact finite Fourier kernel and an attained quadratic value. -/
theorem exists_strict_storage {N : ℕ} (hN : 0<N) {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hε : 0<ε) (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε) :
    ∃ (W : Bilinear (Fin N→E)) (η : ℝ),0<η ∧
      (∀ x y,W x y=W y x) ∧ ∀ (x : Fin N→E) (d : E),
        W (registerStep x d) (registerStep x d)-W x x+instantaneous K x d≤
          -η*((∑ j : Fin N,‖x j‖^2)+‖d‖^2) := by
  let η:=ε/(2*(N+1:ℝ))
  have hη : 0<η:=div_pos hε (by positivity)
  let K':=K++diagonalKernel N η
  have hK' : K'.Supported N:=NatKernel.supported_append hK (diagonalKernel_supported N η)
  have hgap' (θ : FrequencyCircle) : kernelSymbol K'.toKernel θ≤ -(ε/2) := by
    rw [NatKernel.toKernel_append,kernelSymbol_append,diagonalKernel_symbol]
    have he : η*(N+1:ℝ)=ε/2 := by dsimp [η]; field_simp
    rw [he]
    linarith [hgap θ]
  let W : Bilinear (Fin N→E):=storageForm hK' (half_pos hε) hgap'
  refine ⟨W,η,hη,storageForm_symmetric hK' (half_pos hε) hgap',fun x d=>?_⟩
  have hd:=storageForm_dissipation hN hK' (half_pos hε) hgap' x d
  change instantaneous (K++diagonalKernel N η) x d+W (registerStep x d) (registerStep x d)≤W x x at hd
  rw [instantaneous_append,instantaneous_diagonal] at hd
  linarith

end Hilbert
end
end nesterov.IQC.KYP
