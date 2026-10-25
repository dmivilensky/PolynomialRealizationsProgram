import polyak.CertifiedExamples.Plateaus.Source
import polyak.CertifiedExamples.Plateaus.PairJets

/-! The literal lifted duals of the two selected rows. All weights are exact
functions of the scalar determinant root and polynomial first-jet system. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking
open polyak.Certificates.PartII.Plateaus
open scoped BigOperators

def first18 : Fin 2 → ℤ := ![1,-4]
def lifts18 : Fin 2 → ℤ := ![19,14]
def reps18 : Fin 2 → ℤ := ![1,14]
def first21 : Fin 3 → ℤ := ![1,-12,-4]
def lifts21 : Fin 3 → ℤ := ![-20,9,-25]
def reps21 : Fin 3 → ℤ := ![1,9,17]

def slope18 := pairSlope (coefficientVector tuning18) first18 lifts18 coordinates18
def slope21 := pairSlope (coefficientVector tuning21) first21 lifts21 coordinates21
def target18 := pairTarget (coefficientVector tuning18) first18 coordinates18 mu18
def target21 := pairTarget (coefficientVector tuning21) first21 coordinates21 mu21
def moments18 := pairMoments (coefficientVector tuning18) first18 lifts18 coordinates18 mu18
def moments21 := pairMoments (coefficientVector tuning21) first21 lifts21 coordinates21 mu21

def weights18 : Fin 4 → ℝ :=
  ![mu18 0-moments18 0,moments18 0,mu18 1-moments18 1,moments18 1]
def weights21 : Fin 6 → ℝ :=
  ![mu21 0-moments21 0,moments21 0,mu21 1-moments21 1,moments21 1,
    mu21 2-moments21 2,moments21 2]

def lags18 : Finset ℤ := {1,19,-4,14}
def lags21 : Finset ℤ := {1,-20,-12,9,-4,-25}

def dual18 (n : ℤ) : ℝ :=
  if n=1 then weights18 0 else if n=19 then weights18 1 else
  if n= -4 then weights18 2 else if n=14 then weights18 3 else 0

def dual21 (n : ℤ) : ℝ :=
  if n=1 then weights21 0 else if n= -20 then weights21 1 else
  if n= -12 then weights21 2 else if n=9 then weights21 3 else
  if n= -4 then weights21 4 else if n= -25 then weights21 5 else 0

theorem dual18_weighted_sum (f : ℤ → ℝ) :
    (∑ n∈lags18,dual18 n*f n)=∑i,weights18 i*f (row18Lags i) := by
  norm_num [lags18,dual18,row18Lags,Fin.sum_univ_succ]

theorem dual21_weighted_sum (f : ℤ → ℝ) :
    (∑ n∈lags21,dual21 n*f n)=∑i,weights21 i*f (row21Lags i) := by
  norm_num [lags21,dual21,row21Lags,Fin.sum_univ_succ]

theorem weights18_pair (i : Fin 4) : weights18 i=
    pairWeight mu18 moments18 (finProdFinEquiv.symm i) := by
  fin_cases i <;> rfl

theorem weights21_pair (i : Fin 6) : weights21 i=
    pairWeight mu21 moments21 (finProdFinEquiv.symm i) := by
  fin_cases i <;> rfl

theorem lags18_pair (i : Fin 4) : row18Lags i=
    pairLag first18 lifts18 (finProdFinEquiv.symm i) := by
  fin_cases i <;> rfl

theorem lags21_pair (i : Fin 6) : row21Lags i=
    pairLag first21 lifts21 (finProdFinEquiv.symm i) := by
  fin_cases i <;> rfl

theorem polynomial18_eq_indexed : polynomialSymbol tuning18 lags18 dual18=
    indexedSymbol tuning18 row18Lags weights18 := by
  funext c
  exact dual18_weighted_sum (fun n=>dividedLag tuning18 n c)

theorem polynomial21_eq_indexed : polynomialSymbol tuning21 lags21 dual21=
    indexedSymbol tuning21 row21Lags weights21 := by
  funext c
  exact dual21_weighted_sum (fun n=>dividedLag tuning21 n c)

theorem polynomial18_eq_pair : polynomialSymbol tuning18 lags18 dual18=
    pairPolynomial tuning18 first18 lifts18 mu18 moments18 := by
  rw [polynomial18_eq_indexed]
  funext c
  unfold indexedSymbol
  norm_num [pairPolynomial,Fintype.sum_prod_type,Fin.sum_univ_succ,pairWeight,pairLag,
    weights18,first18,lifts18,row18Lags]
  ring

theorem polynomial21_eq_pair : polynomialSymbol tuning21 lags21 dual21=
    pairPolynomial tuning21 first21 lifts21 mu21 moments21 := by
  rw [polynomial21_eq_indexed]
  funext c
  unfold indexedSymbol
  norm_num [pairPolynomial,Fintype.sum_prod_type,Fin.sum_univ_succ,pairWeight,pairLag,
    weights21,first21,lifts21,row21Lags]
  ring

end polyak.CertifiedExamples.Plateaus
