/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Incomparable

/-!
# Coordinate-indexed incomparable encodings

Each complete one-time-signature coordinate has its own message fibre and incomparable code.
No relation between the codes at different coordinates is required.
-/

public section

namespace GXMSS.Encoding

/-- Incomparable encodings indexed by full one-time-signature coordinates. -/
structure Family (I PP : Type) (Message : I → Type) (R : Type) (n radix : ℕ) where
  /-- One incomparable code and fallible encoder for each coordinate and message fibre. -/
  component : (i : I) → IncomparableEncoding PP (Message i) R Unit n radix

namespace Family

variable {I PP R : Type} {Message : I → Type} {n radix : ℕ}

/-- The optional encoded word at one complete coordinate. -/
@[expose] def value (family : Family I PP Message R n radix)
    (i : I) (pp : PP) (msg : Message i) (r : R) : Option (Codeword n radix) :=
  (family.component i).value pp msg r ()

/-- Present a fixed coordinate's encoding to an algorithm with an additional epoch argument.
The full encoding coordinate is already captured by `i`. -/
@[expose] def atEpoch (family : Family I PP Message R n radix) (i : I) (E : Type) :
    IncomparableEncoding PP (Message i) R E n radix where
  code := (family.component i).code
  incomparable := (family.component i).incomparable
  encode pp msg r _ := (family.component i).encode pp msg r ()

/-- Adding an epoch argument preserves the fixed-coordinate word and returned failure. -/
@[simp] theorem value_atEpoch (family : Family I PP Message R n radix)
    (i : I) (E : Type) (pp : PP) (msg : Message i) (r : R) (ep : E) :
    (family.atEpoch i E).value pp msg r ep = family.value i pp msg r := rfl

/-- Every successful output belongs to the code of its own coordinate. -/
theorem mem_code_of_value_eq_some (family : Family I PP Message R n radix)
    (i : I) (pp : PP) (msg : Message i) (r : R) {word : Codeword n radix}
    (h : family.value i pp msg r = some word) : word ∈ (family.component i).code :=
  (family.component i).mem_code_of_value_eq_some pp msg r () h

/-- Distinct outputs at one coordinate are incomparable across all its input choices. -/
theorem incomparableWords_of_successes (family : Family I PP Message R n radix)
    (i : I) (pp pp' : PP) (msg msg' : Message i) (r r' : R)
    {word word' : Codeword n radix}
    (h : family.value i pp msg r = some word)
    (h' : family.value i pp' msg' r' = some word') (hne : word ≠ word') :
    IncomparableWords word word' :=
  (family.component i).incomparableWords_of_successes pp pp' msg msg' r r' () () h h' hne

/-- Every successful word has a digit below the maximum at its own coordinate. -/
@[expose] def NoMaximumOutput (family : Family I PP Message R n radix) : Prop :=
  ∀ i pp msg r word, family.value i pp msg r = some word →
    ∃ j : Fin n, (word j).val < radix - 1

/-- Two distinct codewords at each coordinate suffice for fibrewise non-maximum outputs.
The words need not themselves occur as encoder outputs. -/
theorem noMaximumOutput_of_two_codewords (family : Family I PP Message R n radix)
    (htwo : ∀ i, ∃ x y : Codeword n radix,
      x ∈ (family.component i).code ∧ y ∈ (family.component i).code ∧ x ≠ y) :
    family.NoMaximumOutput := by
  intro i pp msg r word hword
  obtain ⟨x, y, hx, hy, hxy⟩ := htwo i
  have hw := family.mem_code_of_value_eq_some i pp msg r hword
  have hother : ∃ z : Codeword n radix, z ∈ (family.component i).code ∧ word ≠ z := by
    by_cases h : word = x
    · exact ⟨y, hy, by simpa [h] using hxy⟩
    · exact ⟨x, hx, h⟩
  obtain ⟨z, hz, hwz⟩ := hother
  obtain ⟨j, hj⟩ := ((family.component i).incomparable hw hz hwz).1
  exact ⟨j, by have := (z j).isLt; omega⟩

end Family

end GXMSS.Encoding
