import nesterov.Slow.Reduction
import nesterov.Flow.OneSpiral
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecificLimits.Basic

/-! Inverse sampling for a single slow frequency, including its common charge. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def SingleProgram (ε c γ G S C : ℝ) : Prop :=
  |C|≤G ∧ ∀ n : ℕ,1≤n →
    0≤G*(Real.cosh (n*(-c*ε))-Real.cos (n*(ε*γ)))-S*Real.sin (n*(ε*γ))+C*Real.sinh (n*(-c*ε)) ∧
    0≤G*(Real.cosh (n*(-c*ε))-Real.cos (n*(ε*γ)))+S*Real.sin (n*(ε*γ))-C*Real.sinh (n*(-c*ε))

theorem singleProgram_finite_iff (ε c γ G S C : ℝ) :
    Slow.FiniteProgram (fun _ : Fin 1=>(1:ℝ)) (fun _=>ε*γ) (fun _=>G) (fun _=>S) (-c*ε) C ↔
      SingleProgram ε c γ G S C := by simp only [Slow.FiniteProgram,SingleProgram,Fin.sum_univ_one,one_mul]

theorem singleProgram_scale {ε c γ G S C a : ℝ} (ha : 0<a) :
    SingleProgram ε c γ (a*G) (a*S) (a*C) ↔ SingleProgram ε c γ G S C := by
  simp_rw [←singleProgram_finite_iff]
  exact Slow.finiteProgram_scale ha

private theorem increment_ratio {A : Type*} {l : Filter A} {e a : A→ℝ} {a₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (ha : Tendsto a l (𝓝 a₀))
    {f : ℝ→ℝ} {d : ℝ} (hf : HasDerivAt f d 0) :
    Tendsto (fun x=>(f (e x*a x)-f 0)/e x) l (𝓝 (a₀*d)) := by
  have he0 := he.mono_right nhdsWithin_le_nhds
  have harg : Tendsto (fun x=>e x*a x) l (𝓝 0) := by simpa only [zero_mul] using he0.mul ha
  have hd : dslope f 0 0=d := by rw [dslope_same,hf.deriv]
  have hds := (continuousAt_dslope_same.mpr hf.differentiableAt).tendsto.comp harg
  rw [hd] at hds
  apply (ha.mul hds).congr'
  filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
  have hn : e x≠0 := ne_of_gt hx
  have hh := sub_smul_dslope f 0 (e x*a x)
  simp only [sub_zero,smul_eq_mul] at hh
  apply (eq_div_iff hn).mpr
  change a x*dslope f 0 (e x*a x)*e x=f (e x*a x)-f 0
  linear_combination hh

private theorem first_lag_limits {A : Type*} {l : Filter A} {e c γ : A→ℝ} {c₀ γ₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hc : Tendsto c l (𝓝 c₀)) (hγ : Tendsto γ l (𝓝 γ₀)) :
    Tendsto (fun x=>Real.sin (e x*γ x)/e x) l (𝓝 γ₀) ∧
    Tendsto (fun x=>Real.sinh (-c x*e x)/e x) l (𝓝 (-c₀)) ∧
    Tendsto (fun x=>(Real.cosh (-c x*e x)-Real.cos (e x*γ x))/e x) l (𝓝 0) := by
  have hsin := increment_ratio he hγ (Real.hasDerivAt_sin 0)
  have hsinh := increment_ratio he hc.neg (Real.hasDerivAt_sinh 0)
  have hcosh := increment_ratio he hc.neg (Real.hasDerivAt_cosh 0)
  have hcos := increment_ratio he hγ (Real.hasDerivAt_cos 0)
  simp only [Real.sin_zero,Real.cos_zero,Real.sinh_zero,Real.cosh_zero,sub_zero,mul_one,neg_zero,mul_zero] at hsin hsinh hcosh hcos
  refine ⟨hsin,?_,?_⟩
  · convert hsinh using 1
    funext x
    congr 2
    ring
  · convert hcosh.sub hcos using 1
    · funext x
      rw [show e x*(-c x)= -c x*e x by ring,←sub_div]
      congr 1
      ring
    · norm_num

/-- The first lag and minimizer bound already force the limiting charge;
no differentiability of the family or assumed limiting charge is needed. -/
theorem singleProgram_limit_charge {A : Type*} {l : Filter A} [NeBot l]
    {e c γ G S C : A→ℝ} {c₀ γ₀ G₀ S₀ C₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hc : Tendsto c l (𝓝 c₀)) (hγ : Tendsto γ l (𝓝 γ₀))
    (hG : Tendsto G l (𝓝 G₀)) (hS : Tendsto S l (𝓝 S₀)) (hC : Tendsto C l (𝓝 C₀))
    (hp : ∀ᶠ x in l,SingleProgram (e x) (c x) (γ x) (G x) (S x) (C x)) :
    S₀*γ₀+C₀*c₀=0 := by
  obtain ⟨hsin,hsinh,hA⟩ := first_lag_limits he hc hγ
  have hl := ((hG.mul hA).sub (hS.mul hsin)).add (hC.mul hsinh)
  have hu := ((hG.mul hA).add (hS.mul hsin)).sub (hC.mul hsinh)
  have hle : ∀ᶠ x in l,0≤G x*((Real.cosh (-c x*e x)-Real.cos (e x*γ x))/e x)-
      S x*(Real.sin (e x*γ x)/e x)+C x*(Real.sinh (-c x*e x)/e x) := by
    filter_upwards [hp,he.eventually self_mem_nhdsWithin] with x hx he0
    have hh := div_nonneg (hx.2 1 le_rfl).1 he0.le
    simpa only [Nat.cast_one,one_mul,sub_div,add_div,mul_div_assoc] using hh
  have hue : ∀ᶠ x in l,0≤G x*((Real.cosh (-c x*e x)-Real.cos (e x*γ x))/e x)+
      S x*(Real.sin (e x*γ x)/e x)-C x*(Real.sinh (-c x*e x)/e x) := by
    filter_upwards [hp,he.eventually self_mem_nhdsWithin] with x hx he0
    have hh := div_nonneg (hx.2 1 le_rfl).2 he0.le
    simpa only [Nat.cast_one,one_mul,sub_div,add_div,mul_div_assoc] using hh
  have h₁ := ge_of_tendsto hl hle
  have h₂ := ge_of_tendsto hu hue
  nlinarith

theorem floor_grid_tendsto {A : Type*} {l : Filter A} {e : A→ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) {q : ℝ} (hq : 0<q) :
    Tendsto (fun x=>(Nat.floor (q/e x):ℝ)*e x) l (𝓝 q) := by
  have hinv := tendsto_inv_nhdsGT_zero.comp he
  have hh := (tendsto_nat_floor_mul_div_atTop hq.le).comp hinv
  convert! hh using 1
  funext x
  simp only [Function.comp_def,div_eq_mul_inv,inv_inv]

/-- Every compact limit of discrete singleton programs is a genuine flow
one-atom program at every positive real lag. -/
theorem singleProgram_limit_flow {A : Type*} {l : Filter A} [NeBot l]
    {e c γ C : A→ℝ} {θ y c₀ γ₀ C₀ : ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (hc : Tendsto c l (𝓝 c₀)) (hγ : Tendsto γ l (𝓝 γ₀))
    (hC : Tendsto C l (𝓝 C₀)) (hc0 : 0<c₀) (hcQ : c₀<Flow.cQ θ y) (hγ0 : 0≤γ₀)
    {G S : A→ℝ} (hG : Tendsto G l (𝓝 (γ₀^2-Flow.delta θ y c₀)))
    (hS : Tendsto S l (𝓝 ((θ-2*c₀)*γ₀)))
    (hp : ∀ᶠ x in l,SingleProgram (e x) (c x) (γ x) (G x) (S x) (C x)) :
    Flow.OneAtomFeasible θ y c₀ γ₀ := by
  have hcharge := singleProgram_limit_charge he hc hγ hG hS hC hp
  have hCeq : C₀= -γ₀*((θ-2*c₀)*γ₀)/c₀ := by
    apply (eq_div_iff hc0.ne').mpr
    nlinarith [hcharge]
  have hmin := le_of_tendsto_of_tendsto hC.abs hG (hp.mono fun _ h=>h.1)
  have hθ := (Flow.lt_cQ_iff θ y c₀).mp hcQ |>.1
  have hθpos : 0≤θ-2*c₀ := by linarith
  have hineq : c₀*Flow.delta θ y c₀≤(3*c₀-θ)*γ₀^2 := by
    rw [hCeq,abs_div,abs_of_pos hc0,neg_mul,abs_neg,
      abs_of_nonneg (by positivity : 0≤γ₀*((θ-2*c₀)*γ₀))] at hmin
    have hh := (div_le_iff₀ hc0).mp hmin
    nlinarith
  have hlag (q : ℝ) (hq : 0<q) : 0≤Flow.backwardKernel θ y c₀ γ₀ q ∧ 0≤Flow.forwardKernel θ y c₀ γ₀ q := by
    let n : A→ℕ := fun x=>Nat.floor (q/e x)
    let v : A→ℝ := fun x=>(n x:ℝ)*e x
    have hv : Tendsto v l (𝓝 q) := floor_grid_tendsto he hq
    have hn : ∀ᶠ x in l,1≤n x := by
      filter_upwards [he.eventually self_mem_nhdsWithin,
        (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds hq)] with x hx hsmall
      exact (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hx).mpr (by linarith))
    have hcv := (hc.mul hv).neg
    have hγv := hγ.mul hv
    have hcosh := (Real.continuous_cosh.tendsto _).comp hcv
    have hcos := (Real.continuous_cos.tendsto _).comp hγv
    have hsin := (Real.continuous_sin.tendsto _).comp hγv
    have hsinh := (Real.continuous_sinh.tendsto _).comp hcv
    have hl := ((hG.mul (hcosh.sub hcos)).sub (hS.mul hsin)).add (hC.mul hsinh)
    have hu := ((hG.mul (hcosh.sub hcos)).add (hS.mul hsin)).sub (hC.mul hsinh)
    have hle : ∀ᶠ x in l,0≤G x*(Real.cosh (-(c x*v x))-Real.cos (γ x*v x))-
        S x*Real.sin (γ x*v x)+C x*Real.sinh (-(c x*v x)) := by
      filter_upwards [hp,hn] with x hx hn0
      have hnt : (n x:ℝ)*(-c x*e x)= -(c x*v x) := by dsimp [v];ring
      have hnω : (n x:ℝ)*(e x*γ x)=γ x*v x := by dsimp [v];ring
      simpa only [hnt,hnω] using (hx.2 (n x) hn0).1
    have hue : ∀ᶠ x in l,0≤G x*(Real.cosh (-(c x*v x))-Real.cos (γ x*v x))+
        S x*Real.sin (γ x*v x)-C x*Real.sinh (-(c x*v x)) := by
      filter_upwards [hp,hn] with x hx hn0
      have hnt : (n x:ℝ)*(-c x*e x)= -(c x*v x) := by dsimp [v];ring
      have hnω : (n x:ℝ)*(e x*γ x)=γ x*v x := by dsimp [v];ring
      simpa only [hnt,hnω] using (hx.2 (n x) hn0).2
    have h₁ := ge_of_tendsto hl hle
    have h₂ := ge_of_tendsto hu hue
    rw [hCeq,Real.cosh_neg,Real.sinh_neg] at h₁ h₂
    constructor
    · dsimp [Flow.backwardKernel,Flow.kernelA,Flow.kernelB]
      convert h₁ using 1
      ring
    · dsimp [Flow.forwardKernel,Flow.kernelA,Flow.kernelB]
      convert h₂ using 1
      ring
  exact ⟨fun q hq=>(hlag q hq).2,fun q hq=>(hlag q hq).1,hineq⟩

end
end nesterov.TwoStep
