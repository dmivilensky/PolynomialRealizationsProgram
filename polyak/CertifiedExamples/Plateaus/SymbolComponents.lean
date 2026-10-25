import polyak.CertifiedExamples.Plateaus.Polynomial
import polyak.Numerics.Polynomial

/-! Executable rational component polynomials, derived from the independent
Chebyshev and removable-quotient sources. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Engine

def qneg (p:QPoly) : QPoly := QPoly.mul (QPoly.constant (-1)) p
def qsub (p q:QPoly) : QPoly := p.add (qneg q)
def twiceX : QPoly := (QPoly.constant 2).mul QPoly.X

def wPair : ℕ→QPoly×QPoly
  | 0=>(QPoly.zero,QPoly.constant 1)
  | n+1=>let p:=wPair n
    (p.2,(QPoly.constant 2).add (qsub (twiceX.mul p.2) p.1))

def uPair : ℕ→QPoly×QPoly
  | 0=>(QPoly.constant 1,twiceX)
  | n+1=>let p:=uPair n
    (p.2,qsub (twiceX.mul p.2) p.1)

def componentCode (n:ℤ) (i:Fin 4) : QPoly :=
  match i.val with
  | 0=>(wPair n.natAbs).1
  | 1=>QPoly.X.mul (wPair n.natAbs).1
  | 2=>(QPoly.X.mul QPoly.X).mul (wPair n.natAbs).1
  | _=>(QPoly.constant (-(n.sign:ℚ))).mul
      (((QPoly.constant 1).add QPoly.X).mul (uPair (n.natAbs-1)).1)

noncomputable section
open Polynomial General Levels
open scoped Polynomial

private theorem W_zero (c:ℝ) : ModeLocking.TwoLag.W 0 c=0 := by
  by_cases h:c=1
  · simp [h,ModeLocking.TwoLag.W_one]
  · rw [ModeLocking.TwoLag.W_quotient 0 h]
    norm_num [Spectral.chebT]

private theorem W_first (c:ℝ) : ModeLocking.TwoLag.W 1 c=1 := by
  by_cases h:c=1
  · simp [h,ModeLocking.TwoLag.W_one]
  · rw [ModeLocking.TwoLag.W_quotient 1 h]
    norm_num [Spectral.chebT]
    exact sub_ne_zero.mpr (Ne.symm h)

private theorem W_next (n:ℕ) (c:ℝ) :
    ModeLocking.TwoLag.W (n+2) c=2+2*c*ModeLocking.TwoLag.W (n+1) c-ModeLocking.TwoLag.W n c := by
  by_cases h:c=1
  · subst c
    simp only [ModeLocking.TwoLag.W_one,Nat.cast_add,Nat.cast_ofNat]
    ring
  · have ht:=congrArg (fun p:ℝ[X]=>p.eval c) (Polynomial.Chebyshev.T_add_two ℝ (n:ℤ))
    have ht' : Spectral.chebT (n+2) c=2*c*Spectral.chebT (n+1) c-Spectral.chebT n c := by
      simpa only [Spectral.chebT,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Int.cast_natCast] using ht
    have h0:=ModeLocking.TwoLag.W_identity n c
    have h1:=ModeLocking.TwoLag.W_identity (n+1) c
    have h2:=ModeLocking.TwoLag.W_identity (n+2) c
    have hm : (1-c)*(ModeLocking.TwoLag.W (n+2) c-
        (2+2*c*ModeLocking.TwoLag.W (n+1) c-ModeLocking.TwoLag.W n c))=0 := by
      linear_combination h2-2*c*h1+h0-ht'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (Ne.symm h)))

theorem wPair_value (n:ℕ) (c:ℝ) :
    Polynomial.aeval c (wPair n).1.toPoly=ModeLocking.TwoLag.W n c ∧
      Polynomial.aeval c (wPair n).2.toPoly=ModeLocking.TwoLag.W (n+1) c := by
  induction n with
  | zero=>simp [wPair,QPoly.toPoly_zero,QPoly.toPoly_constant,W_zero,W_first]
  | succ n ih=>
    simp only [wPair]
    refine ⟨ih.2,?_⟩
    simp only [qsub,qneg,twiceX,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
      QPoly.toPoly_X,map_add,map_mul,Polynomial.aeval_X,ih.1,ih.2,
      map_ofNat,map_neg,map_one]
    rw [show n+1+1=n+2 by omega,W_next]
    ring

theorem uPair_value (n:ℕ) (c:ℝ) :
    Polynomial.aeval c (uPair n).1.toPoly=Spectral.chebU n c ∧
      Polynomial.aeval c (uPair n).2.toPoly=Spectral.chebU (n+1) c := by
  induction n with
  | zero=>norm_num [uPair,twiceX,QPoly.toPoly_constant,QPoly.toPoly_mul,QPoly.toPoly_X,Spectral.chebU]
  | succ n ih=>
    simp only [uPair]
    refine ⟨ih.2,?_⟩
    have ht:=congrArg (fun p:ℝ[X]=>p.eval c) (Polynomial.Chebyshev.U_add_two ℝ (n:ℤ))
    have ht' : Spectral.chebU (n+2) c=2*c*Spectral.chebU (n+1) c-Spectral.chebU n c := by
      simpa only [Spectral.chebU,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Int.cast_natCast] using ht
    simp only [qsub,qneg,twiceX,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
      QPoly.toPoly_X,map_add,map_mul,Polynomial.aeval_X,ih.1,ih.2,
      map_ofNat,map_neg,map_one]
    rw [show n+1+1=n+2 by omega,ht']
    ring

def componentValue (n:ℤ) (i:Fin 4) (c:ℝ) : ℝ :=
  if i.val=0 then ModeLocking.TwoLag.W n.natAbs c
  else if i.val=1 then c*ModeLocking.TwoLag.W n.natAbs c
  else if i.val=2 then c^2*ModeLocking.TwoLag.W n.natAbs c
  else -(n.sign:ℝ)*(1+c)*Spectral.chebU (n.natAbs-1) c

theorem componentCode_value (n:ℤ) (i:Fin 4) (c:ℝ) :
    Polynomial.aeval c (componentCode n i).toPoly=componentValue n i c := by
  fin_cases i <;>
    simp [componentCode,componentValue,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
      QPoly.toPoly_X,(wPair_value _ _).1,(uPair_value _ _).1,pow_two]
  ring

end
end polyak.CertifiedExamples.Plateaus
