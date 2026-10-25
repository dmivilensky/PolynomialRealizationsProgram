import polyak.FiniteHorizon.SegmentClass
import polyak.Growth.Tail

/-!
Article: Appendix C, scalar profiles in the proof of Lemma plateauclass.
Use: limit profiles retain the forward envelope bounds and finite energy
inequalities; no continuation inside the original class is used.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Finset Filter
open scoped Topology

def ProfileEnergy (b : ℕ → ℝ) (K : ℝ) (w : ℕ) : Prop :=
  ∀ i j,w≤ i → i≤j → mass b i (j+1)≤K*(energyWindow b w i+energyWindow b w j)

def ProfileForward (g b : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ i k,b (i+k)≤g k*(b i+Real.exp (2*t)*b (i+1))

theorem mass_le_local_boundary {b : ℕ → ℝ} (hb : ∀ k,0≤b k) (hsub : Subexponential b)
    {K : ℝ} (hK : 0<K) {w : ℕ} (he : ProfileEnergy b K w) (i j : ℕ) :
    mass b i j≤(1+2*K)*mass b i (i+2*w+1) := by
  have hw : energyWindow b w (i+w)=mass b i (i+2*w+1):=by
    unfold energyWindow
    rw [Nat.add_sub_cancel]
    congr 1
    omega
  have hleft : mass b i (i+w)≤mass b i (i+2*w+1):=mass_mono hb le_rfl (by omega)
  have hmass:=mass_nonneg hb i (i+2*w+1)
  by_cases hj : i+w≤j
  · have hh:=mass_le_boundary hb hsub hK w (i+w)
      (fun l hl => he (i+w) l (by omega) hl) j hj
    rw [hw] at hh
    have hs:=mass_add (b:=b) (show i≤ i+w by omega) hj
    nlinarith
  · have hm : mass b i j≤mass b i (i+2*w+1):=mass_mono hb le_rfl (by omega)
    nlinarith

theorem mass_local_of_forward {g b : ℕ → ℝ} {t : ℝ}
    (hf : ProfileForward g b t) (i m : ℕ) :
    mass b i (i+m)≤(∑ k∈Ico 0 m,g k)*(b i+Real.exp (2*t)*b (i+1)) := by
  have he : mass b i (i+m)=mass (fun k => b (i+k)) 0 m:=by
    unfold mass
    simpa only [zero_add,Nat.add_comm] using (sum_Ico_add b 0 m i).symm
  rw [he,mass,sum_mul]
  exact sum_le_sum fun k _ => hf i k

theorem exists_profile_mass_bound (g : ℕ → ℝ) (hg : ∀ k,0≤g k) (t : ℝ)
    {K : ℝ} (hK : 0<K) (w : ℕ) :
    ∃ D : ℝ,1<D ∧ ∀ b : ℕ → ℝ,(∀ k,0≤b k) → Subexponential b →
      ProfileEnergy b K w → ProfileForward g b t →
        ∀ i j,mass b i j≤D*(b i+b (i+1)) := by
  let C:=1+∑ k∈Ico 0 (2*w+1),g k
  have hC : 1≤C:=by
    dsimp [C]
    exact le_add_of_nonneg_right (sum_nonneg fun k _ => hg k)
  let D:=2+(1+2*K)*C*(1+Real.exp (2*t))
  have hD : 1<D:=by
    have hh : 0<(1+2*K)*C*(1+Real.exp (2*t)):=by positivity
    dsimp [D]
    linarith
  refine ⟨D,hD,fun b hb hsub he hf i j => ?_⟩
  have hlocal:=mass_local_of_forward hf i (2*w+1)
  have hprefix:=mass_le_local_boundary hb hsub hK he i j
  have hpair : b i+Real.exp (2*t)*b (i+1)≤(1+Real.exp (2*t))*(b i+b (i+1)):=by
    nlinarith [hb i,hb (i+1),mul_nonneg (Real.exp_pos (2*t)).le (hb i)]
  have hbound : mass b i j≤(1+2*K)*C*(1+Real.exp (2*t))*(b i+b (i+1)):=by
    calc
      _≤(1+2*K)*mass b i (i+2*w+1):=hprefix
      _≤(1+2*K)*((∑ k∈Ico 0 (2*w+1),g k)*(b i+Real.exp (2*t)*b (i+1))):=by
        have hh : i+(2*w+1)=i+2*w+1:=by omega
        rw [hh] at hlocal
        exact mul_le_mul_of_nonneg_left hlocal (by linarith)
      _≤(1+2*K)*C*((1+Real.exp (2*t))*(b i+b (i+1))):=by
        rw [mul_assoc (1+2*K) C]
        apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ)≤1+2*K)
        apply mul_le_mul
        · dsimp [C]
          linarith
        · exact hpair
        · exact add_nonneg (hb i) (mul_nonneg (Real.exp_pos (2*t)).le (hb (i+1)))
        · linarith
      _=_:=by ring
  dsimp [D]
  nlinarith [hb i,hb (i+1)]

/-- One fixed positive horizon contracts every infinite scalar limit profile. -/
theorem exists_profile_contraction (g : ℕ → ℝ) (hg : ∀ k,0≤g k) (t : ℝ)
    {K : ℝ} (hK : 0<K) (w : ℕ) :
    ∃ P : ℕ,0<P ∧ ∀ b : ℕ → ℝ,(∀ k,0≤b k) → (∀ k,b k≤g k) → Subexponential b →
      ProfileEnergy b K w → ProfileForward g b t → b P+Real.exp (2*t)*b (P+1)≤1/4 := by
  obtain ⟨D,hD,hbound⟩:=exists_profile_mass_bound g hg t hK w
  let θ:=1-1/D
  have hθ : 0≤θ:=by
    have hh:=(div_le_one (zero_lt_one.trans hD)).mpr hD.le
    dsimp [θ]
    linarith
  have hθ1 : θ<1:=by dsimp [θ]; linarith [one_div_pos.mpr (zero_lt_one.trans hD)]
  let M:=(1+Real.exp (2*t))*D*(g 0+g 1)
  have hl : Tendsto (fun p : ℕ => M*θ^p) atTop (𝓝 0):=by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).const_mul M
  obtain ⟨p,hp,hp0⟩:=((hl.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))).and
    (eventually_gt_atTop 0)).exists
  refine ⟨2*p,by omega,fun b hb hbg hsub he hf => ?_⟩
  have hh:=pair_le_geometric hb hD (fun i j _ => hbound b hb hsub he hf i j) p
  have hfirst : b 0+b 1≤g 0+g 1:=add_le_add (hbg 0) (hbg 1)
  have hpair : b (2*p)+Real.exp (2*t)*b (2*p+1)≤
      (1+Real.exp (2*t))*(b (2*p)+b (2*p+1)):=by
    nlinarith [hb (2*p),hb (2*p+1),mul_nonneg (Real.exp_pos (2*t)).le (hb (2*p))]
  have hm:=mul_le_mul_of_nonneg_left hh (show 0≤1+Real.exp (2*t) by positivity)
  have hi:=mul_le_mul_of_nonneg_left hfirst
    (show 0≤(1+Real.exp (2*t))*θ^p*D by positivity)
  dsimp [M] at hp
  change _≤θ^p*D*(b 0+b 1) at hh
  nlinarith

namespace SegmentClass
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

def profileWeight (t : ℝ) (k : ℕ) : ℝ:=Real.exp (-2*(k : ℝ)*t)*G.envelope k^2

theorem profileWeight_nonneg (t : ℝ) (k : ℕ) : 0≤G.profileWeight t k:=by
  unfold profileWeight
  positivity

theorem profileWeight_subexponential {r : ℝ} (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r)) :
    Subexponential (G.profileWeight (Real.log r)) := by
  intro δ hδ
  have hR : r<Real.exp (Real.log r+δ/2):=by
    calc
      r=Real.exp (Real.log r):=(Real.exp_log hr).symm
      _<Real.exp (Real.log r+δ/2):=Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨C,hC,hbound⟩:=G.exists_exponential_majorant hpos hr hlim hR
  refine ⟨C^2,by positivity,fun k => ?_⟩
  have hh:=(sq_le_sq₀ (hpos k).le (by positivity : 0≤C*Real.exp (Real.log r+δ/2)^k)).mpr (hbound k)
  have hm:=mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*(k : ℝ)*Real.log r)).le
  have he : Real.exp (-2*(k : ℝ)*Real.log r)*(C*Real.exp (Real.log r+δ/2)^k)^2=
      C^2*Real.exp (δ*k):=by
    rw [←Real.exp_nat_mul]
    calc
      _=C^2*(Real.exp (-2*(k : ℝ)*Real.log r)*Real.exp ((k : ℝ)*(Real.log r+δ/2))*
          Real.exp ((k : ℝ)*(Real.log r+δ/2))):=by ring
      _=C^2*Real.exp ((-2*(k : ℝ)*Real.log r+(k : ℝ)*(Real.log r+δ/2))+
          (k : ℝ)*(Real.log r+δ/2)):=by rw [←Real.exp_add,←Real.exp_add]
      _=_:=by congr 2; ring
  exact hm.trans_eq he

end SegmentClass
end polyak.FiniteHorizon
