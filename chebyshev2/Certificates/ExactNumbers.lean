import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
Article: chebyshev2, Section 4.1.
Exact decoding of the decimal, rational and hexadecimal dyadic tokens in SINEJACOBI_PROOF_3.
Use: `chebyshev2.Certificates.DecodedBytes` feeds
`chebyshev2.Certificates.DualInputs.Reference.source_bytes` (source bytes).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates
set_option autoImplicit false

/--
Defines `digit` of type `Option ℕ` by `if '0'≤c ∧ c≤'9' then some (c.toNat-'0'.toNat) else if
'a'≤c ∧ c≤'f' then some (10+c.toNat-'a'.toNat) else if 'A'≤c ∧ c≤'F' then some
(10+c.toNat-'A'.toNat) else none`.

Use: `chebyshev2.Certificates.unsigned` uses this definition in the displayed construction
of `unsigned`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def digit (c : Char) : Option ℕ :=
  if '0'≤c ∧ c≤'9' then some (c.toNat-'0'.toNat)
  else if 'a'≤c ∧ c≤'f' then some (10+c.toNat-'a'.toNat)
  else if 'A'≤c ∧ c≤'F' then some (10+c.toNat-'A'.toNat) else none

/--
Defines `unsigned` of type `Option ℕ` by `do if cs.isEmpty then none else cs.foldlM (fun n c =>
do let d ← digit c if d<base then some (base*n+d) else none) 0`.

Use: `chebyshev2.Certificates.mantissa` uses this definition in the displayed construction
of `mantissa`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def unsigned (base : ℕ) (cs : List Char) : Option ℕ := do
  if cs.isEmpty then none else
    cs.foldlM (fun n c => do
      let d ← digit c
      if d<base then some (base*n+d) else none) 0

/--
Defines `signedInteger` by pattern matching with result type `List Char → Option ℤ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Certificates.scaledMantissa` uses this definition in the displayed
construction of `scaledMantissa`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def signedInteger : List Char → Option ℤ
  | '-'::cs => (unsigned 10 cs).map (fun n => -(n:ℤ))
  | '+'::cs => (unsigned 10 cs).map (fun n => (n:ℤ))
  | cs => (unsigned 10 cs).map (fun n => (n:ℤ))

/--
Defines `scaleExact` of type `ℚ` by `if 0≤exponent then base^exponent.toNat else
1/base^(-exponent).toNat`.

Use: `chebyshev2.Certificates.binary64` uses this definition in the displayed construction
of `binary64`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def scaleExact (base : ℚ) (exponent : ℤ) : ℚ :=
  if 0≤exponent then base^exponent.toNat else 1/base^(-exponent).toNat

/--
Defines `mantissa` of type `Option ℚ` by `match cs.splitOn '.' with | [whole] => (unsigned base
whole).map (fun n => (n:ℚ)) | [whole,frac] => do let n ← unsigned base (whole++frac) if
whole.isEmpty ∨ frac.isEmpty then none else some ((n:ℚ)/(base:ℚ)^frac.length) | _ => none`.

Use: `chebyshev2.Certificates.scaledMantissa` uses this definition in the displayed
construction of `scaledMantissa`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def mantissa (base : ℕ) (cs : List Char) : Option ℚ :=
  match cs.splitOn '.' with
  | [whole] => (unsigned base whole).map (fun n => (n:ℚ))
  | [whole,frac] => do
    let n ← unsigned base (whole++frac)
    if whole.isEmpty ∨ frac.isEmpty then none else some ((n:ℚ)/(base:ℚ)^frac.length)
  | _ => none

/--
Defines `scaledMantissa` of type `Option ℚ` by `match cs.splitOn separator with | [m] =>
mantissa base m | [m,e] => do let q ← mantissa base m let exponent ← signedInteger e some
(q*scaleExact (if base=16 then 2 else base) exponent) | _ => none`.

Use: `chebyshev2.Certificates.unsignedNumber` uses this definition in the displayed
construction of `unsignedNumber`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def scaledMantissa (base : ℕ) (separator : Char) (cs : List Char) : Option ℚ :=
  match cs.splitOn separator with
  | [m] => mantissa base m
  | [m,e] => do
    let q ← mantissa base m
    let exponent ← signedInteger e
    some (q*scaleExact (if base=16 then 2 else base) exponent)
  | _ => none

/--
Defines `unsignedNumber` by pattern matching with result type `List Char → Option ℚ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Certificates.numberBody` uses this definition in the displayed
construction of `numberBody`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def unsignedNumber : List Char → Option ℚ
  | '0'::'x'::cs => scaledMantissa 16 'p' cs
  | cs => scaledMantissa 10 'e' cs

/--
Defines `numberBody` of type `Option ℚ` by `match cs.splitOn '/' with | [n] => unsignedNumber n
| [n,d] => do let a ← unsigned 10 n let b ← unsigned 10 d if b=0 then none else some ((a:ℚ)/b)
| _ => none`.

Use: `chebyshev2.Certificates.exactChars` uses this definition in the displayed
construction of `exactChars`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def numberBody (cs : List Char) : Option ℚ :=
  match cs.splitOn '/' with
  | [n] => unsignedNumber n
  | [n,d] => do
    let a ← unsigned 10 n
    let b ← unsigned 10 d
    if b=0 then none else some ((a:ℚ)/b)
  | _ => none

/--
Defines `exactChars` by pattern matching with result type `List Char → Option ℚ`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.Certificates.exactBytes` uses this definition in the displayed
construction of `exactBytes`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def exactChars : List Char → Option ℚ
  | '-'::cs => (numberBody cs).map Neg.neg
  | '+'::cs => numberBody cs
  | cs => numberBody cs

/--
Defines `exactNumber` of type `Option ℚ` by `exactChars token.toList`.

Use: `chebyshev2.Certificates.numberTokens_cons` uses this definition to establish
acceptance/decoding identity for the displayed finite data: `numberTokens (token::tokens)=some
(q::qs)`.

Article: chebyshev2, Section 4.1.
-/
def exactNumber (token : String) : Option ℚ := exactChars token.toList

/--
Proof computation uses ASCII bytes directly, avoiding normalization of Lean's UTF-8 array
implementation on long archive strings.

Use: `chebyshev2.Certificates.byteNumbers` uses this definition in the displayed
construction of `byteNumbers`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def exactBytes (bytes : List ℕ) : Option ℚ :=
  if bytes.any (fun b => decide (128≤b)) then none else exactChars (bytes.map Char.ofNat)

/--
Defines `numericByteTokens` of type `List (List ℕ)` by `(bytes.splitOnP (fun b => b==32 || b==9
|| b==10 || b==13)).filter (fun token => token.head?.any (fun b => (decide (48≤b) && decide
(b≤57)) || b==43 || b==45))`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def numericByteTokens (bytes : List ℕ) : List (List ℕ) :=
  (bytes.splitOnP (fun b => b==32 || b==9 || b==10 || b==13)).filter
    (fun token => token.head?.any (fun b => (decide (48≤b) && decide (b≤57)) || b==43 || b==45))

/--
Defines `byteNumbers` by pattern matching with result type `List (List ℕ) → Option (List ℚ)`.
The displayed branches determine the recursive cases and their returned values.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def byteNumbers : List (List ℕ) → Option (List ℚ)
  | [] => some []
  | token::tokens => do
    let q ← exactBytes token
    let qs ← byteNumbers tokens
    some (q::qs)

/--
An exact source-decoding record. The data retain the original text/bytes, numeric tokens and
rational values; proof fields check the complete tokenization and decoding correspondence.

Use: `chebyshev2.Certificates.Compact.AmplitudeValues.ValidPanel.actual` uses this record
of data and proof obligations to establish `(p.valuePanel scale
epsilon).Actual scale integrand`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure DecodedBytes where
  /-- Original source bytes, retained so tokenization is checked in Lean. -/
  bytes : List ℕ
  /-- Numeric tokens extracted from the original bytes/text; each token is decoded exactly. -/
  tokens : List (List ℕ)
  /-- Exact rational values corresponding to the numeric tokens. -/
  values : List ℚ
  /-- Proof that the stored source tokenizes to precisely the stored token list. -/
  tokenized : numericByteTokens bytes=tokens
  /-- Proof that exact token decoding returns precisely the stored rational values. -/
  decoded : byteNumbers tokens=some values

/--
Defines `textTokens` of type `List String` by `((text.toList.splitOnP Char.isWhitespace).filter
(fun cs => !cs.isEmpty)).map String.ofList`.

Use: `chebyshev2.Certificates.numericTokens` uses this definition in the displayed
construction of `numericTokens`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Section 4.1.
-/
def textTokens (text : String) : List String :=
  ((text.toList.splitOnP Char.isWhitespace).filter (fun cs => !cs.isEmpty)).map String.ofList

/--
Defines `numericTokens` of type `List String` by `(textTokens text).filter (fun token =>
token.toList.head?.any (fun c => c.isDigit || c=='+' || c=='-'))`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.
-/
def numericTokens (text : String) : List String :=
  (textTokens text).filter (fun token => token.toList.head?.any
    (fun c => c.isDigit || c=='+' || c=='-'))

/--
Defines `numberTokens` by pattern matching with result type `List String → Option (List ℚ)`.
The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Certificates.numberTokens_cons` rewrites with this definition to establish
acceptance/decoding identity for the displayed finite data: `numberTokens (token::tokens)=some
(q::qs)`.

Article: chebyshev2, Section 4.1.
-/
def numberTokens : List String → Option (List ℚ)
  | [] => some []
  | token::tokens => do
    let q ← exactNumber token
    let qs ← numberTokens tokens
    some (q::qs)

 /--
Acceptance/decoding identity for the displayed finite data: `numberTokens (token::tokens)=some
(q::qs)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem numberTokens_cons {token : String} {tokens : List String} {q : ℚ} {qs : List ℚ}
    (h : exactNumber token=some q) (hs : numberTokens tokens=some qs) :
    numberTokens (token::tokens)=some (q::qs) := by simp [numberTokens,h,hs]

/--
A decoder assertion can be kernel-checked independently of the exporter.

Use: a standalone supporting record of data and proof obligations for the article chain below;
no retained declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.
-/
structure DecodedNumbers where
  /-- Numeric tokens extracted from the original bytes/text; each token is decoded exactly. -/
  tokens : List String
  /-- Exact rational values corresponding to the numeric tokens. -/
  values : List ℚ
  /-- Proof that exact token decoding returns precisely the stored rational values. -/
  decoded : numberTokens tokens=some values


/--
An exact source-decoding record. The data retain the original text/bytes, numeric tokens and
rational values; proof fields check the complete tokenization and decoding correspondence.

Use: a standalone supporting record of data and proof obligations for the article chain below;
no retained declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.
-/
structure DecodedText extends DecodedNumbers where
  /-- Original textual source whose numeric tokenization is checked. -/
  text : String
  /-- Proof that the stored source tokenizes to precisely the stored token list. -/
  tokenized : numericTokens text=tokens

/--
Finite IEEE-754 binary64 values decoded by integer arithmetic, including subnormals and signed
zero. Infinity and NaN are rejected.

Use: `chebyshev2.Certificates.binary64LE` uses this definition in the displayed
construction of `binary64LE`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def binary64 (bits : ℕ) : Option ℚ := do
  if bits≥2^64 then none else
    let exponent : ℕ := bits/2^52%2048
    if exponent=2047 then none else
      let mantissa : ℕ := bits%2^52 + if exponent=0 then 0 else 2^52
      let shift : ℤ := if exponent=0 then -1074 else (exponent:ℤ)-1075
      let value := (mantissa:ℚ)*scaleExact 2 shift
      some (if bits/2^63=0 then value else -value)

/--
Defines `littleEndian` by pattern matching with result type `List ℕ → Option ℕ`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.Certificates.binary64LE` uses this definition in the displayed
construction of `binary64LE`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def littleEndian : List ℕ → Option ℕ
  | [] => some 0
  | b::bs => do
    if b≥256 then none else
      let rest ← littleEndian bs
      some (b+256*rest)

/--
Defines `binary64LE` of type `Option ℚ` by `do if bytes.length≠8 then none else binary64 (←
littleEndian bytes)`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.
-/
def binary64LE (bytes : List ℕ) : Option ℚ := do
  if bytes.length≠8 then none else binary64 (← littleEndian bytes)

end chebyshev2.Certificates
