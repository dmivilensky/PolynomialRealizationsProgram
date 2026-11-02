import bezout.Models.CycleFourier
import bezout.Comparisons.RootAsymptotics.Limits
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
Article: bezout, the full real active network spectrum in Appendix D.
Use: the displayed cycle frequencies give the exact strict interior modes;
the physical cycle admits a genuine real orthonormal spectral coordinate map.
Proof: the finite Fourier equivalence identifies all real eigenspaces, while
the real self-adjoint spectral theorem supplies the orthonormal coordinates.
-/

namespace bezout.Models.Network
noncomputable section
open scoped BigOperators
open Polynomial
variable (m : ℕ) [NeZero m]

/-- The canonical cyclic angle lies in one half-open full period. -/
theorem cycleAngle_mem (j : ZMod m) :
    0≤2*Real.pi*(j.val:ℝ)/m ∧ 2*Real.pi*(j.val:ℝ)/m<2*Real.pi := by
  have hm : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  constructor
  · positivity
  · apply (div_lt_iff₀ hm).mpr
    have hj : (j.val:ℝ)<m := by exact_mod_cast j.val_lt
    nlinarith [Real.pi_pos]

/-- Only the constant cyclic frequency has Laplacian eigenvalue zero. -/
theorem cycleEigenvalue_eq_zero (j : ZMod m) : cycleEigenvalue m j=0 ↔ j=0 := by
  have ha := cycleAngle_mem m j
  have hc := Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos] :
    -(2*Real.pi)<2*Real.pi*(j.val:ℝ)/m) ha.2
  constructor
  · intro h
    have hcos : Real.cos (2*Real.pi*(j.val:ℝ)/m)=1 := by
      unfold cycleEigenvalue at h
      linarith
    have hz := hc.mp hcos
    have hm : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
    have hv : (j.val:ℝ)=0 := by
      have ht := (div_eq_zero_iff.mp hz).resolve_right hm
      nlinarith [Real.pi_pos]
    have hv' : j.val=0 := by exact_mod_cast hv
    rw [← ZMod.natCast_zmod_val j,hv']
    simp
  · rintro rfl
    exact cycleEigenvalue_zero m

/-- At an even nonzero cycle only its alternating frequency has eigenvalue four. -/
theorem cycleEigenvalue_eq_four (hm : Even m) (j : ZMod m) :
    cycleEigenvalue m j=4 ↔ j=((m/2:ℕ):ZMod m) := by
  have ha := cycleAngle_mem m j
  have hangle : 2*Real.pi*(j.val:ℝ)/m-Real.pi=0 ↔ cycleEigenvalue m j=4 := by
    have hc := Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [Real.pi_pos] : -(2*Real.pi)<2*Real.pi*(j.val:ℝ)/m-Real.pi)
      (by linarith [Real.pi_pos] : 2*Real.pi*(j.val:ℝ)/m-Real.pi<2*Real.pi)
    rw [← hc,Real.cos_sub,Real.cos_pi,Real.sin_pi]
    unfold cycleEigenvalue
    constructor <;> intro h <;> nlinarith
  constructor
  · intro h
    have ht := hangle.mpr h
    have hm0 : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
    have ht' := (div_eq_iff hm0).mp (show 2*Real.pi*(j.val:ℝ)/m=Real.pi by linarith)
    have hv : 2*j.val=m := by
      have hv' : 2*(j.val:ℝ)=m := by nlinarith [Real.pi_pos]
      exact_mod_cast hv'
    have hj : j.val=m/2 := by omega
    rw [← ZMod.natCast_zmod_val j,hj]
  · rintro rfl
    exact cycleEigenvalue_half m hm

/-- Every other cyclic mode is strictly interior to the two Laplacian endpoints. -/
theorem cycleEigenvalue_strict (hm : Even m) (j : ZMod m)
    (h0 : j≠0) (hhalf : j≠((m/2:ℕ):ZMod m)) :
    cycleEigenvalue m j ∈ Set.Ioo (0:ℝ) 4 := by
  have hb := cycleEigenvalue_mem m j
  exact ⟨lt_of_le_of_ne hb.1 (Ne.symm (fun h => h0 ((cycleEigenvalue_eq_zero m j).mp h))),
    lt_of_le_of_ne hb.2 (fun h => hhalf ((cycleEigenvalue_eq_four m hm j).mp h))⟩

/-- The actual real Euclidean cycle operator, before any spectral coordinates are chosen. -/
def cycleOperator : EuclideanSpace ℝ (ZMod m) →ₗ[ℝ] EuclideanSpace ℝ (ZMod m) :=
  (WithLp.linearEquiv 2 ℝ (ZMod m → ℝ)).symm.toLinearMap.comp
    ((cycleLaplacian m).comp (WithLp.linearEquiv 2 ℝ (ZMod m → ℝ)).toLinearMap)

omit [NeZero m] in
/-- Literal coordinate action of the actual Euclidean cycle Laplacian. -/
@[simp] theorem cycleOperator_apply (u : EuclideanSpace ℝ (ZMod m)) (i : ZMod m) :
    cycleOperator m u i=2*u i-u (i+1)-u (i-1) := rfl

/-- The two cyclic shifts are exact adjoints under the physical Euclidean inner product. -/
theorem shift_inner (u v : EuclideanSpace ℝ (ZMod m)) :
    (∑ i,u (i+1)*v i)=∑ i,u i*v (i-1) := by
  have h := Equiv.sum_comp (Equiv.addRight (1:ZMod m)) (fun i => u i*v (i-1))
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using h

/-- The physical real cycle is self-adjoint; the real spectral theorem therefore applies. -/
theorem cycleOperator_symmetric : (cycleOperator m).IsSymmetric := by
  intro u v
  change inner ℝ (cycleOperator m u) v=inner ℝ u (cycleOperator m v)
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    cycleOperator_apply,sub_mul,mul_sub,Finset.sum_sub_distrib]
  have h1 := shift_inner m u v
  have h2 := shift_inner m v u
  have h1' : (∑ i,v i*u (i+1))=∑ i,v (i-1)*u i := by
    simpa only [mul_comm] using h1
  have h2' : (∑ i,v i*u (i-1))=∑ i,v (i+1)*u i := h2.symm
  rw [h1',h2']
  have hd : (∑ i,v i*(2*u i))=∑ i,2*v i*u i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  ring

/-- Complex Fourier coordinates of an actual real Euclidean cycle state. -/
def realFourier (u : EuclideanSpace ℝ (ZMod m)) : ZMod m → ℂ :=
  (cycleSynthesis m).symm (fun i => (u i:ℂ))

/-- Reconstructing the real state's complex Fourier coordinates recovers the state. -/
@[simp] theorem realFourier_reconstruct (u : EuclideanSpace ℝ (ZMod m)) :
    cycleSynthesis m (realFourier m u)=fun i => (u i:ℂ) :=
  (cycleSynthesis m).apply_symm_apply _

/-- Every Fourier coordinate of a real eigenstate obeys the displayed scalar eigenvalue equation. -/
theorem real_eigen_fourier (u : EuclideanSpace ℝ (ZMod m)) (lam : ℝ)
    (hu : cycleOperator m u=lam • u) (j : ZMod m) :
    (cycleEigenvalue m j:ℂ)*realFourier m u j=(lam:ℂ)*realFourier m u j := by
  have hz : complexCycle m (fun i => (u i:ℂ))=(lam:ℂ) • (fun i => (u i:ℂ)) := by
    funext i
    have h := congrArg (fun v : EuclideanSpace ℝ (ZMod m) => (v i:ℂ)) hu
    simpa only [complexCycle,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,
      cycleOperator_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_sub,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using h
  have hh : cycleSynthesis m (fun j => (cycleEigenvalue m j:ℂ)*realFourier m u j)=
      cycleSynthesis m ((lam:ℂ) • realFourier m u) := by
    rw [← cycle_diagonalization,realFourier_reconstruct,hz,map_smul,realFourier_reconstruct]
  exact congrFun ((cycleSynthesis m).injective hh) j

/-- Every real cycle eigenvalue is one of the explicitly displayed cosine values. -/
theorem real_eigenvalue_eq_cosine (u : EuclideanSpace ℝ (ZMod m)) (hu0 : u≠0) (lam : ℝ)
    (hu : cycleOperator m u=lam • u) : ∃ j : ZMod m,lam=cycleEigenvalue m j := by
  have hc : realFourier m u≠0 := by
    intro h
    apply hu0
    ext i
    have hi := congrFun (realFourier_reconstruct m u) i
    rw [h,map_zero] at hi
    change u i=0
    apply Complex.ofReal_injective
    simpa using hi.symm
  have hex : ∃ j,realFourier m u j≠0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,?_⟩
  exact Complex.ofReal_injective ((mul_right_cancel₀ hj (real_eigen_fourier m u lam hu j)).symm)

/-- A cycle eigenspace supported on one Fourier frequency is an actual real one-dimensional line. -/
theorem real_eigenline (j0 : ZMod m) (lam : ℝ)
    (hunique : ∀ j,cycleEigenvalue m j=lam → j=j0)
    (u : EuclideanSpace ℝ (ZMod m)) (hu : cycleOperator m u=lam • u) (i : ZMod m) :
    u i=u 0*cycleMode m j0 i := by
  have hc (j : ZMod m) (hj : j≠j0) : realFourier m u j=0 := by
    have he := real_eigen_fourier m u lam hu j
    by_contra hz
    have hval : cycleEigenvalue m j=lam :=
      Complex.ofReal_injective (mul_right_cancel₀ hz he)
    exact hj (hunique j hval)
  have hform (i : ZMod m) : (u i:ℂ)=
      (m:ℂ)⁻¹*(realFourier m u j0*complexMode m j0 i) := by
    have hf := congrFun (cycleSynthesis_expansion m (realFourier m u)) i
    rw [realFourier_reconstruct] at hf
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] at hf
    rw [Finset.sum_eq_single j0] at hf
    · exact hf
    · intro j _ hj
      rw [hc j hj,zero_mul]
    · simp
  have h0 := hform 0
  simp only [complexMode,mul_zero,AddChar.map_zero_eq_one,mul_one] at h0
  have hh : (u i:ℂ)=(u 0:ℂ)*complexMode m j0 i := by
    rw [hform,h0]
    ring
  have hr := congrArg Complex.re hh
  simpa only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,
    complexMode,cycleMode] using hr

/-- The actual physical real cycle has an orthonormal basis of real eigenvectors. -/
def realEigenbasis : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (ZMod m)) :=
  (cycleOperator_symmetric m).eigenvectorBasis (by simp)

/-- Corresponding actual real cycle eigenvalues, with full multiplicity. -/
def realEigenvalue : Fin m → ℝ :=
  (cycleOperator_symmetric m).eigenvalues (by simp)

/-- Every chosen real orthonormal mode is an eigenvector of the actual cycle. -/
theorem realEigenbasis_eigenvector (j : Fin m) :
    cycleOperator m (realEigenbasis m j)=realEigenvalue m j • realEigenbasis m j :=
  (cycleOperator_symmetric m).apply_eigenvectorBasis _ j

/-- Every chosen real orthonormal mode has one of the actual Fourier cosine eigenvalues. -/
theorem realEigenvalue_cosine (j : Fin m) :
    ∃ k : ZMod m,realEigenvalue m j=cycleEigenvalue m k := by
  exact real_eigenvalue_eq_cosine m _ ((realEigenbasis m).orthonormal.ne_zero j) _
    (realEigenbasis_eigenvector m j)

/-- Genuine real orthonormal spectral coordinates diagonalize the actual cycle operator. -/
theorem realEigenbasis_diagonalization (u : EuclideanSpace ℝ (ZMod m)) (j : Fin m) :
    (realEigenbasis m).repr (cycleOperator m u) j=
      realEigenvalue m j*(realEigenbasis m).repr u j :=
  (cycleOperator_symmetric m).eigenvectorBasis_apply_self_apply _ u j

/-- A simple Fourier frequency occurs only once in the actual real orthonormal eigenbasis. -/
theorem realEigenvalue_unique (j0 : ZMod m) (lam : ℝ)
    (hunique : ∀ j,cycleEigenvalue m j=lam → j=j0)
    {i j : Fin m} (hi : realEigenvalue m i=lam) (hj : realEigenvalue m j=lam) : i=j := by
  let v : EuclideanSpace ℝ (ZMod m) := WithLp.toLp 2 (cycleMode m j0)
  have hvi : realEigenbasis m i=(realEigenbasis m i 0) • v := by
    ext k
    exact real_eigenline m j0 lam hunique _
      (by rw [← hi]; exact realEigenbasis_eigenvector m i) k
  have hvj : realEigenbasis m j=(realEigenbasis m j 0) • v := by
    ext k
    exact real_eigenline m j0 lam hunique _
      (by rw [← hj]; exact realEigenbasis_eigenvector m j) k
  have hi0 : realEigenbasis m i 0≠0 := by
    intro hz
    have h := hvi
    rw [hz,zero_smul] at h
    exact (realEigenbasis m).orthonormal.ne_zero i h
  have hj0 : realEigenbasis m j 0≠0 := by
    intro hz
    have h := hvj
    rw [hz,zero_smul] at h
    exact (realEigenbasis m).orthonormal.ne_zero j h
  have hv0 : v≠0 := by
    intro hz
    have h := hvi
    rw [hz,smul_zero] at h
    exact (realEigenbasis m).orthonormal.ne_zero i h
  by_contra hij
  have ho : inner ℝ (realEigenbasis m i) (realEigenbasis m j)=0 := by
    simpa only [hij,ite_false] using orthonormal_iff_ite.mp (realEigenbasis m).orthonormal i j
  rw [hvi,hvj,inner_smul_left,inner_smul_right] at ho
  simp only [conj_trivial] at ho
  exact (mul_ne_zero hi0 (mul_ne_zero hj0 (ne_of_gt (real_inner_self_pos.mpr hv0)))) ho

/-- Every displayed real cycle mode is an actual Euclidean eigenvector. -/
theorem cycleMode_euclidean_eigenvector (j : ZMod m) :
    cycleOperator m (WithLp.toLp 2 (cycleMode m j))=
      cycleEigenvalue m j • WithLp.toLp 2 (cycleMode m j) := by
  ext i
  exact congrFun (cycle_mode_eigenvector m j) i

/-- Every cosine frequency occurs among the genuine real orthonormal spectral values. -/
theorem realEigenvalue_exists (j : ZMod m) :
    ∃ i : Fin m,realEigenvalue m i=cycleEigenvalue m j := by
  apply (cycleOperator_symmetric m).exists_eigenvalues_eq (by simp)
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_,?_⟩
  · exact (Module.End.mem_eigenspace_iff).mpr (cycleMode_euclidean_eigenvector m j)
  · intro hz
    apply cycleMode_ne_zero m j
    have h := congrArg WithLp.ofLp hz
    exact h

/-- The unique lower endpoint index in genuine real orthonormal spectral coordinates. -/
def lowerMode : Fin m := (realEigenvalue_exists m 0).choose

/-- The unique upper endpoint index in genuine real orthonormal spectral coordinates. -/
def upperMode : Fin m := (realEigenvalue_exists m ((m/2:ℕ):ZMod m)).choose

/-- The lower chosen coordinate is exactly the constant Laplacian mode. -/
@[simp] theorem lowerMode_value : realEigenvalue m (lowerMode m)=0 := by
  exact (realEigenvalue_exists m 0).choose_spec.trans (cycleEigenvalue_zero m)

/-- At an even horizon the upper chosen coordinate is exactly the alternating mode. -/
theorem upperMode_value (hm : Even m) : realEigenvalue m (upperMode m)=4 := by
  exact (realEigenvalue_exists m ((m/2:ℕ):ZMod m)).choose_spec.trans (cycleEigenvalue_half m hm)

/-- The two physical endpoint spectral coordinates are distinct. -/
theorem endpointModes_distinct (hm : Even m) : lowerMode m≠upperMode m := by
  intro h
  have hh := lowerMode_value m
  rw [h,upperMode_value m hm] at hh
  norm_num at hh

/-- Exactly the chosen lower coordinate has real orthonormal eigenvalue zero. -/
theorem realEigenvalue_eq_zero (j : Fin m) : realEigenvalue m j=0 ↔ j=lowerMode m := by
  constructor
  · intro hj
    exact realEigenvalue_unique m 0 0 (fun k hk => (cycleEigenvalue_eq_zero m k).mp hk)
      hj (lowerMode_value m)
  · rintro rfl
    exact lowerMode_value m

/-- Exactly the chosen upper coordinate has real orthonormal eigenvalue four. -/
theorem realEigenvalue_eq_four (hm : Even m) (j : Fin m) :
    realEigenvalue m j=4 ↔ j=upperMode m := by
  constructor
  · intro hj
    exact realEigenvalue_unique m _ 4 (fun k hk => (cycleEigenvalue_eq_four m hm k).mp hk)
      hj (upperMode_value m hm)
  · rintro rfl
    exact upperMode_value m hm

/-- Every remaining genuine real orthonormal mode is strictly interior. -/
theorem realEigenvalue_strict (hm : Even m) (j : Fin m)
    (hj0 : j≠lowerMode m) (hj1 : j≠upperMode m) : realEigenvalue m j∈Set.Ioo (0:ℝ) 4 := by
  obtain ⟨k,hk⟩ := realEigenvalue_cosine m j
  have hb := cycleEigenvalue_mem m k
  rw [← hk] at hb
  refine ⟨lt_of_le_of_ne hb.1 (Ne.symm ?_),lt_of_le_of_ne hb.2 ?_⟩
  · exact fun h => hj0 ((realEigenvalue_eq_zero m j).mp h)
  · exact fun h => hj1 ((realEigenvalue_eq_four m hm j).mp h)

/-- The actual active network interval for a symbolic condition number. -/
def cycleInterval (κ : ℝ) (hκ : 1<κ) : chebyshev1.SpectralInterval :=
  ⟨1/κ,1,one_div_pos.mpr (by linarith),(div_lt_one (by linarith : (0:ℝ)<κ)).mpr hκ⟩

/-- The active spectral value attached to a genuine real orthonormal cycle mode. -/
def activeSpectralValue (κ : ℝ) (j : Fin m) : ℝ :=
  (realEigenvalue m j+2*(2/(κ-1)))/(4+2*(2/(κ-1)))

/-- The genuine real spectral basis supplies the generalized endpoint-plus-bulk signal.
Only the prescribed initial amplitudes are parameters; no spectral conclusion is assumed. -/
def cycleFiniteSignal (κ : ℝ) (hκ : 1<κ) (hm : Even m) (a : Fin m → ℝ) (w : ℝ)
    (hw : 0<w) (ha0 : a (lowerMode m)^2=w) (ha1 : a (upperMode m)^2=w) :
    Comparisons.RootAsymptotics.FiniteSignal (cycleInterval κ hκ) (Fin m) where
  eigenvalue := activeSpectralValue m κ
  amplitude := a
  lower := lowerMode m
  upper := upperMode m
  distinct := endpointModes_distinct m hm
  lower_value := by
    unfold activeSpectralValue
    rw [lowerMode_value]
    exact (active_endpoints κ hκ).1
  upper_value := by
    unfold activeSpectralValue
    rw [upperMode_value m hm]
    exact (active_endpoints κ hκ).2
  mass := w
  mass_pos := hw
  lower_mass := ha0
  upper_mass := ha1
  interior j hj0 hj1 := by
    have hb := realEigenvalue_strict m hm j hj0 hj1
    change |(cycleInterval κ hκ).z
      ((realEigenvalue m j+2*(2/(κ-1)))/(4+2*(2/(κ-1))))|<1
    unfold cycleInterval
    rw [chart_cancellation κ (realEigenvalue m j) hκ]
    exact abs_lt.mpr ⟨by linarith [hb.2],by linarith [hb.1]⟩

end
end bezout.Models.Network
