import nesterov.Realization.ScalarStartup
import nesterov.Realization.Potential
import nesterov.Momentum.Stationary

/-!
Article: Lemma `lem:startup`, the physical from-rest executor.
Use: the repaired query table determines the actual momentum iterates, with
one decaying scalar coordinate and the prescribed latent wave coordinates.
-/
namespace nesterov.Realization
noncomputable section
open polyak.Realization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def physical (W : ℕ→E) (β τ h lam Y : ℝ) (n : ℕ) : WithLp 2 (E×ℝ) :=
  WithLp.toLp 2 (W (n+1),Y*Momentum.iterate (fun x : ℝ=>lam*x) β τ h 1 n)

def waveQuery (W : ℕ→E) (τ : ℝ) : Option ℕ→E
  | none => 0
  | some k => W (k+1)+τ • (W (k+1)-W k)

def firstGradient (W : ℕ→E) (h : ℝ) : E := (1/h) • (W 1-W 2)

def repairedQuery (W : ℕ→E) (β τ h lam Y : ℝ) (k : ℕ) : WithLp 2 (E×ℝ) :=
  productPosition (correctPosition (waveQuery W τ) (W 1))
    (scalarPosition (scalarQuery β τ h lam) Y) (some k)

@[simp] theorem repairedQuery_zero (W : ℕ→E) (β τ h lam Y : ℝ) :
    repairedQuery W β τ h lam Y 0=physical W β τ h lam Y 0 := by
  simp [repairedQuery,physical,productPosition,correctPosition,scalarPosition]

theorem physical_query (W : ℕ→E) (β τ h lam Y : ℝ) (n : ℕ) :
    physical W β τ h lam Y (n+1)+τ •
      (physical W β τ h lam Y (n+1)-physical W β τ h lam Y n)=
        repairedQuery W β τ h lam Y (n+1) := by
  apply WithLp.ofLp_injective 2
  have hn : (some (n+1):Option ℕ)≠some 0 := by simp
  simp only [physical,repairedQuery,productPosition,correctPosition,scalarPosition,hn,
    WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul]
  apply Prod.ext
  · rfl
  · change Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 (n+1)+
        τ*(Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 (n+1)-
          Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 n)=Y*scalarQuery β τ h lam (n+1)
    rw [scalarQuery_eq_actual,Momentum.queryIterate_succ]
    simp only [smul_eq_mul]
    ring

theorem iterate_eq_of_recurrence (g : E→E) (β τ h : ℝ) (X : ℕ→E)
    (hfirst : X 1=X 0-h • g (X 0))
    (hrec : ∀ n,X (n+2)=X (n+1)+β • (X (n+1)-X n)-
      h • g (X (n+1)+τ • (X (n+1)-X n))) :
    ∀ n,Momentum.iterate g β τ h (X 0) n=X n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simpa only [Momentum.iterate_one] using hfirst.symm
  | more n ih ih' =>
    rw [Momentum.iterate_recurrence,Momentum.queryIterate_succ,ih,ih',hrec n]

theorem physical_iterate (W G : ℕ→E) (β τ h lam Y : ℝ) (hh : h≠0)
    (hW : ∀ k,W (k+2)=W (k+1)+β • (W (k+1)-W k)-h • G k)
    (g : WithLp 2 (E×ℝ)→WithLp 2 (E×ℝ))
    (hdata : ∀ k,g (repairedQuery W β τ h lam Y k)=
      WithLp.toLp 2 (if k=0 then firstGradient W h else G k,lam*(Y*scalarQuery β τ h lam k))) :
    ∀ n,Momentum.iterate g β τ h (physical W β τ h lam Y 0) n=physical W β τ h lam Y n := by
  apply iterate_eq_of_recurrence
  · rw [←repairedQuery_zero,hdata]
    apply WithLp.ofLp_injective 2
    simp only [physical,repairedQuery,productPosition,correctPosition,scalarPosition,
      scalarQuery_zero,ite_eq_left,WithLp.ofLp_sub,WithLp.ofLp_smul]
    apply Prod.ext
    · change W 2=W 1-h • firstGradient W h
      dsimp [firstGradient]
      rw [smul_smul,mul_one_div_cancel hh,one_smul]
      module
    · simp [Momentum.iterate_one,smul_eq_mul]
      ring
  · intro n
    rw [physical_query,hdata]
    apply WithLp.ofLp_injective 2
    have hn : n+1≠0 := by omega
    simp only [physical,hn,WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul]
    apply Prod.ext
    · exact hW (n+1)
    · change Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 (n+2)=
        Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 (n+1)+
        β*(Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 (n+1)-
          Y*Momentum.iterate (fun x:ℝ=>lam*x) β τ h 1 n)-h*(lam*(Y*scalarQuery β τ h lam (n+1)))
      rw [Momentum.iterate_recurrence,scalarQuery_eq_actual]
      simp only [smul_eq_mul]
      ring

end
end nesterov.Realization
