import krylov.Certificates.EndpointComparison

/-!
Article: main_krylov, apC:prop:digits, exact endpoint rational witness.
The rational functions below are bounded barriers for the compactified gap
with x=1/U. Every witness coefficient is literal rational data. The two LV
residual signs are exact Bernstein identities checked by ring normalization;
no floating point computation or proposed trajectory is trusted.
Source: elementary rational differential barriers and Bernstein positivity.
-/
namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact degree-seven compactified witness endpointNumerator. -/
def endpointNumerator (x : ℝ) : ℝ := (5999999381 / 2000000000) * x ^ 0 + (970171331193 / 5000000000) * x ^ 1 + (7817397373151 / 2000000000) * x ^ 2 + (301521325207097 / 10000000000) * x ^ 3 + (91864638035557 / 1000000000) * x ^ 4 + (52927213285577 / 500000000) * x ^ 5 + (25276404260279 / 625000000) * x ^ 6 + (35959006309097 / 10000000000) * x ^ 7

/-- Literal polynomial derivative. -/
def endpointNumeratorDerivative (x : ℝ) : ℝ := (970171331193 / 5000000000) * x ^ 0 + (7817397373151 / 1000000000) * x ^ 1 + (904563975621291 / 10000000000) * x ^ 2 + (91864638035557 / 250000000) * x ^ 3 + (52927213285577 / 100000000) * x ^ 4 + (75829212780837 / 312500000) * x ^ 5 + (251713044163679 / 10000000000) * x ^ 6

/-- Ordinary polynomial differentiation of the exact data. -/
theorem endpointNumerator_hasDerivAt (x : ℝ) :
    HasDerivAt endpointNumerator (endpointNumeratorDerivative x) x := by
  have h0 := ((hasDerivAt_id x).pow 0).const_mul (5999999381 / 2000000000)
  have h1 := h0.add (((hasDerivAt_id x).pow 1).const_mul (970171331193 / 5000000000))
  have h2 := h1.add (((hasDerivAt_id x).pow 2).const_mul (7817397373151 / 2000000000))
  have h3 := h2.add (((hasDerivAt_id x).pow 3).const_mul (301521325207097 / 10000000000))
  have h4 := h3.add (((hasDerivAt_id x).pow 4).const_mul (91864638035557 / 1000000000))
  have h5 := h4.add (((hasDerivAt_id x).pow 5).const_mul (52927213285577 / 500000000))
  have h6 := h5.add (((hasDerivAt_id x).pow 6).const_mul (25276404260279 / 625000000))
  have h7 := h6.add (((hasDerivAt_id x).pow 7).const_mul (35959006309097 / 10000000000))
  convert h7 using 1
  · rfl
  · norm_num [endpointNumeratorDerivative]
    ring

/-- Exact degree-seven compactified witness endpointDenominator. -/
def endpointDenominator (x : ℝ) : ℝ := 1 * x ^ 0 + (137355947691 / 2000000000) * x ^ 1 + (3804108364877 / 2500000000) * x ^ 2 + (134389954874331 / 10000000000) * x ^ 3 + (243114047731169 / 5000000000) * x ^ 4 + (683147284250093 / 10000000000) * x ^ 5 + (321811746781579 / 10000000000) * x ^ 6 + (6941253635249 / 2000000000) * x ^ 7

/-- Literal polynomial derivative. -/
def endpointDenominatorDerivative (x : ℝ) : ℝ := (137355947691 / 2000000000) * x ^ 0 + (3804108364877 / 1250000000) * x ^ 1 + (403169864622993 / 10000000000) * x ^ 2 + (243114047731169 / 1250000000) * x ^ 3 + (683147284250093 / 2000000000) * x ^ 4 + (965435240344737 / 5000000000) * x ^ 5 + (48588775446743 / 2000000000) * x ^ 6

/-- Ordinary polynomial differentiation of the exact data. -/
theorem endpointDenominator_hasDerivAt (x : ℝ) :
    HasDerivAt endpointDenominator (endpointDenominatorDerivative x) x := by
  have h0 := ((hasDerivAt_id x).pow 0).const_mul 1
  have h1 := h0.add (((hasDerivAt_id x).pow 1).const_mul (137355947691 / 2000000000))
  have h2 := h1.add (((hasDerivAt_id x).pow 2).const_mul (3804108364877 / 2500000000))
  have h3 := h2.add (((hasDerivAt_id x).pow 3).const_mul (134389954874331 / 10000000000))
  have h4 := h3.add (((hasDerivAt_id x).pow 4).const_mul (243114047731169 / 5000000000))
  have h5 := h4.add (((hasDerivAt_id x).pow 5).const_mul (683147284250093 / 10000000000))
  have h6 := h5.add (((hasDerivAt_id x).pow 6).const_mul (321811746781579 / 10000000000))
  have h7 := h6.add (((hasDerivAt_id x).pow 7).const_mul (6941253635249 / 2000000000))
  convert h7 using 1
  · rfl
  · norm_num [endpointDenominatorDerivative]
    ring

/-- Positive denominator on the whole compactified physical interval. -/
theorem endpointDenominator_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < endpointDenominator x := by
  unfold endpointDenominator
  positivity

/-- The rational center stays in the enlarged bounded comparison strip,
even after either exact error allowance is added. -/
theorem endpointRational_strip {x : ℝ} (hx : 0 ≤ x) :
    1 + 1 / 500000 ≤ endpointNumerator x / endpointDenominator x ∧
      endpointNumerator x / endpointDenominator x ≤ 4 - 1 / 500000 := by
  have hq := endpointDenominator_pos hx
  constructor
  · apply (le_div_iff₀ hq).mpr
    have h : 0 ≤ endpointNumerator x - (1 + 1 / 500000) * endpointDenominator x := by
      unfold endpointNumerator endpointDenominator
      ring_nf
      positivity
    linarith
  · apply (div_le_iff₀ hq).mpr
    have h : 0 ≤ (4 - 1 / 500000) * endpointDenominator x - endpointNumerator x := by
      unfold endpointNumerator endpointDenominator
      ring_nf
      positivity
    linarith

/-- The numerator of the compactified LV residual of the shifted rational graph.
Its denominator is the positive cube of endpointDenominator. -/
def endpointRationalResidual (x c : ℝ) : ℝ :=
  x ^ 2 * (endpointNumerator x + c * endpointDenominator x + endpointDenominator x) *
    (endpointNumeratorDerivative x * endpointDenominator x -
      endpointNumerator x * endpointDenominatorDerivative x) +
  (endpointNumerator x + c * endpointDenominator x - 3 * endpointDenominator x) *
    endpointDenominator x ^ 2 +
  2 * x * (endpointNumerator x + c * endpointDenominator x) *
    (endpointNumerator x + c * endpointDenominator x - endpointDenominator x) *
    endpointDenominator x

/-- Exact Bernstein certificate for the lower rational barrier residual. -/
theorem endpointRationalResidual_lower {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    endpointRationalResidual x (-(1 / 500000)) ≤ 0 := by
  have hx₀ := hx.1
  have hx₁ : 0 ≤ 1 - x := by linarith [hx.2]
  let P : ℝ :=
    (4619 / 2000000000) * x ^ 0 * (1 - x) ^ 22 +
    (22972674776973 / 125000000000000000) * x ^ 1 * (1 - x) ^ 21 +
    (11371510740437022224428367 / 125000000000000000000000000) * x ^ 2 * (1 - x) ^ 20 +
    (5762580947212753983315238670028077 / 2000000000000000000000000000000000) * x ^ 3 * (1 - x) ^ 19 +
    (63251231025284936565500091853511272939629 / 1000000000000000000000000000000000000000) * x ^ 4 * (1 - x) ^ 18 +
    (13470742702881762587771179004679237294876283 / 2500000000000000000000000000000000000000) * x ^ 5 * (1 - x) ^ 17 +
    (762357662598624846491518871110586219005617837 / 6250000000000000000000000000000000000000) * x ^ 6 * (1 - x) ^ 16 +
    (72233075027244215771355933779086829159683377769 / 62500000000000000000000000000000000000000) * x ^ 7 * (1 - x) ^ 15 +
    (1144762104591213558802571225846575669595851518779 / 62500000000000000000000000000000000000000) * x ^ 8 * (1 - x) ^ 14 +
    (29857760072081977399352650778515917482935508837377 / 125000000000000000000000000000000000000000) * x ^ 9 * (1 - x) ^ 13 +
    (199191483349835054798235865464318729330075778335737 / 125000000000000000000000000000000000000000) * x ^ 10 * (1 - x) ^ 12 +
    (139034898642369311186957653749345658041679147580281 / 15625000000000000000000000000000000000000) * x ^ 11 * (1 - x) ^ 11 +
    (1480827066457765965271938813803012117117834473737491 / 31250000000000000000000000000000000000000) * x ^ 12 * (1 - x) ^ 10 +
    (2842041155081246267492835237210088794614204597352977 / 15625000000000000000000000000000000000000) * x ^ 13 * (1 - x) ^ 9 +
    (64785698248524391283641589276685595798230167104271983 / 125000000000000000000000000000000000000000) * x ^ 14 * (1 - x) ^ 8 +
    (4728102062022532134711323528655681151698214894256803 / 3906250000000000000000000000000000000000) * x ^ 15 * (1 - x) ^ 7 +
    (276995222305102808120665465409921147320728831909021067 / 125000000000000000000000000000000000000000) * x ^ 16 * (1 - x) ^ 6 +
    (3783484619082163578224232298481593943833054965743907 / 1250000000000000000000000000000000000000) * x ^ 17 * (1 - x) ^ 5 +
    (193550002027106207638512847304313688797912098569621247 / 62500000000000000000000000000000000000000) * x ^ 18 * (1 - x) ^ 4 +
    (288719924402178801645192820918100058875655371971014281 / 125000000000000000000000000000000000000000) * x ^ 19 * (1 - x) ^ 3 +
    (145085991325283179542088720750281871118118145357811943 / 125000000000000000000000000000000000000000) * x ^ 20 * (1 - x) ^ 2 +
    (44468453260377358221631534356736815815106464220046281 / 125000000000000000000000000000000000000000) * x ^ 21 * (1 - x) ^ 1 +
    (6232163624220884080716683705242692641387046851154851 / 125000000000000000000000000000000000000000) * x ^ 22 * (1 - x) ^ 0
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have he : endpointRationalResidual x (-(1 / 500000)) = -P := by
    dsimp only [endpointRationalResidual, endpointNumerator, endpointNumeratorDerivative,
      endpointDenominator, endpointDenominatorDerivative, P]
    ring
  rw [he]
  linarith

/-- Exact Bernstein certificate for the upper rational barrier residual. -/
theorem endpointRationalResidual_upper {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ endpointRationalResidual x ((1 / 500000)) := by
  have hx₀ := hx.1
  have hx₁ : 0 ≤ 1 - x := by linarith [hx.2]
  let P : ℝ :=
    (3381 / 2000000000) * x ^ 0 * (1 - x) ^ 22 +
    (96044285372277 / 125000000000000000) * x ^ 1 * (1 - x) ^ 21 +
    (1369976973950535694239133 / 125000000000000000000000000) * x ^ 2 * (1 - x) ^ 20 +
    (7263622381428763382119830179572077 / 2000000000000000000000000000000000) * x ^ 3 * (1 - x) ^ 19 +
    (214905276910917134712303988839980023860371 / 1000000000000000000000000000000000000000) * x ^ 4 * (1 - x) ^ 18 +
    (7607315002541656892959640460805014279423717 / 2500000000000000000000000000000000000000) * x ^ 5 * (1 - x) ^ 17 +
    (413288854727443296405992057727429941201982163 / 6250000000000000000000000000000000000000) * x ^ 6 * (1 - x) ^ 16 +
    (125469489799937218598290702434635801978825872231 / 62500000000000000000000000000000000000000) * x ^ 7 * (1 - x) ^ 15 +
    (1402175637990780554207186729837304685720793231221 / 62500000000000000000000000000000000000000) * x ^ 8 * (1 - x) ^ 14 +
    (20983573294319638405448242500757599032678352162623 / 125000000000000000000000000000000000000000) * x ^ 9 * (1 - x) ^ 13 +
    (197007408851394358492565394824017815179428835664263 / 125000000000000000000000000000000000000000) * x ^ 10 * (1 - x) ^ 12 +
    (163814026658394723833123555880509571603739222607219 / 15625000000000000000000000000000000000000) * x ^ 11 * (1 - x) ^ 11 +
    (1433385659633868281552297087951023995239978057262509 / 31250000000000000000000000000000000000000) * x ^ 12 * (1 - x) ^ 10 +
    (2676009675736622955951350193371373668925202896459523 / 15625000000000000000000000000000000000000) * x ^ 13 * (1 - x) ^ 9 +
    (66523689046266114309091791041744167206548966354728017 / 125000000000000000000000000000000000000000) * x ^ 14 * (1 - x) ^ 8 +
    (2405543684112021326351045807978988304531116454660661 / 1953125000000000000000000000000000000000) * x ^ 15 * (1 - x) ^ 7 +
    (272723694783117142569693140241430964574882578810978933 / 125000000000000000000000000000000000000000) * x ^ 16 * (1 - x) ^ 6 +
    (3777907719515838143296612165325391694379047557216093 / 1250000000000000000000000000000000000000) * x ^ 17 * (1 - x) ^ 5 +
    (194988104083116483466887933387243914149804666289378753 / 62500000000000000000000000000000000000000) * x ^ 18 * (1 - x) ^ 4 +
    (287370506777610027372684047589822879922805187185985719 / 125000000000000000000000000000000000000000) * x ^ 19 * (1 - x) ^ 3 +
    (145312715586914752472657630868952186934864042735188057 / 125000000000000000000000000000000000000000) * x ^ 20 * (1 - x) ^ 2 +
    (44455246387663645099625682247117770562255297883953719 / 125000000000000000000000000000000000000000) * x ^ 21 * (1 - x) ^ 1 +
    (6232352760520786123483554713818778446795425007345149 / 125000000000000000000000000000000000000000) * x ^ 22 * (1 - x) ^ 0
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have he : endpointRationalResidual x ((1 / 500000)) = P := by
    dsimp only [endpointRationalResidual, endpointNumerator, endpointNumeratorDerivative,
      endpointDenominator, endpointDenominatorDerivative, P]
    ring
  rw [he]
  linarith

end
end krylov.Certificates
