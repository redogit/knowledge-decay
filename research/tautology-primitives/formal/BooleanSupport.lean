import BasisCertificates

/-!
# Complete representation of ordered binary Boolean operations

The numeric operation type is in bijection with all total functions
`Bool → Bool → Bool`. The four input positions are retained in the order
00, 01, 10, 11, with the first entry carrying weight eight. The classification
lemmas below partition the operations by their diagonal unary function.
-/

namespace FIG22.Basis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Encode the ordered truth vector 00, 01, 10, 11. -/
def encodeBits (b00 b01 b10 b11 : Bool) : Op :=
  ⟨8 * b00.toNat + 4 * b01.toNat + 2 * b10.toNat + b11.toNat, by
    cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide⟩

/-- Encode any total binary Boolean function without imposing a symmetry. -/
def encodeTruthTable (f : Bool → Bool → Bool) : Op :=
  encodeBits (f false false) (f false true) (f true false) (f true true)

theorem applyOp_encodeBits (b00 b01 b10 b11 a b : Bool) :
    applyOp (encodeBits b00 b01 b10 b11) a b =
      if a then (if b then b11 else b10) else (if b then b01 else b00) := by
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
    cases a <;> cases b <;> decide

@[simp] theorem applyOp_encodeTruthTable (f : Bool → Bool → Bool) (a b : Bool) :
    applyOp (encodeTruthTable f) a b = f a b := by
  unfold encodeTruthTable
  rw [applyOp_encodeBits]
  cases a <;> cases b <;> rfl

@[simp] theorem encodeTruthTable_applyOp (h : Op) :
    encodeTruthTable (applyOp h) = h := by
  have all : ∀ k : Op, encodeTruthTable (applyOp k) = k := by decide
  exact all h

theorem applyOp_injective : Function.Injective applyOp := by
  intro h k heq
  have hc := congrArg encodeTruthTable heq
  simpa only [encodeTruthTable_applyOp] using hc

theorem applyOp_surjective : Function.Surjective applyOp := by
  intro f
  refine ⟨encodeTruthTable f, ?_⟩
  funext a b
  exact applyOp_encodeTruthTable f a b

theorem applyOp_eq_iff (h k : Op) : applyOp h = applyOp k ↔ h = k :=
  ⟨fun heq => applyOp_injective heq, fun heq => congrArg applyOp heq⟩

/-- Both ordered off-diagonal entries are required to identify an operation. -/
theorem applyOp_ext {h k : Op}
    (h00 : applyOp h false false = applyOp k false false)
    (h01 : applyOp h false true = applyOp k false true)
    (h10 : applyOp h true false = applyOp k true false)
    (h11 : applyOp h true true = applyOp k true true) : h = k := by
  apply applyOp_injective
  funext a b
  cases a <;> cases b
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- An explicit inverse pair certifies coverage of all binary Boolean functions. -/
theorem binaryFunction_bijection :
    (∀ h : Op, encodeTruthTable (applyOp h) = h) ∧
    (∀ f : Bool → Bool → Bool, applyOp (encodeTruthTable f) = f) := by
  constructor
  · exact encodeTruthTable_applyOp
  · intro f
    funext a b
    exact applyOp_encodeTruthTable f a b

theorem applyOp_bijective : Function.Injective applyOp ∧ Function.Surjective applyOp :=
  ⟨applyOp_injective, applyOp_surjective⟩

theorem encodeTruthTable_injective : Function.Injective encodeTruthTable := by
  intro f g heq
  funext a b
  have he := congrArg (fun h => applyOp h a b) heq
  simpa only [applyOp_encodeTruthTable] using he

theorem truthVector_orientation (h : Op) :
    h.val = 8 * (applyOp h false false).toNat +
      4 * (applyOp h false true).toNat +
      2 * (applyOp h true false).toNat + (applyOp h true true).toNat := by
  have heq := congrArg Fin.val (encodeTruthTable_applyOp h)
  exact heq.symm

theorem diagonal_zero_iff (h : Op) :
    compose h .var .var = .zero ↔ h = 0 ∨ h = 2 ∨ h = 4 ∨ h = 6 := by
  have all : ∀ k : Op,
      compose k .var .var = .zero ↔ k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 := by decide
  exact all h

theorem diagonal_var_iff (h : Op) :
    compose h .var .var = .var ↔ h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 7 := by
  have all : ∀ k : Op,
      compose k .var .var = .var ↔ k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by decide
  exact all h

theorem diagonal_neg_iff (h : Op) :
    compose h .var .var = .neg ↔ h = 8 ∨ h = 10 ∨ h = 12 ∨ h = 14 := by
  have all : ∀ k : Op,
      compose k .var .var = .neg ↔ k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14 := by decide
  exact all h

theorem diagonal_one_iff (h : Op) :
    compose h .var .var = .one ↔ h = 9 ∨ h = 11 ∨ h = 13 ∨ h = 15 := by
  have all : ∀ k : Op,
      compose k .var .var = .one ↔ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15 := by decide
  exact all h

theorem diagonal_partition (h : Op) :
    compose h .var .var = .zero ∨ compose h .var .var = .var ∨
      compose h .var .var = .neg ∨ compose h .var .var = .one := by
  cases compose h .var .var <;> simp

theorem zeroPreserving_iff (h : Op) :
    applyOp h false false = false ↔ h.val < 8 := by
  have all : ∀ k : Op, applyOp k false false = false ↔ k.val < 8 := by decide
  exact all h

theorem selfDual_iff (h : Op) :
    (∀ a b : Bool, applyOp h (!a) (!b) = !(applyOp h a b)) ↔
      h = 3 ∨ h = 5 ∨ h = 10 ∨ h = 12 := by
  have all : ∀ k : Op,
      (∀ a b : Bool, applyOp k (!a) (!b) = !(applyOp k a b)) ↔
        k = 3 ∨ k = 5 ∨ k = 10 ∨ k = 12 := by decide
  exact all h

/-! ## Cost-preserving representation of arbitrary function-labelled formulas -/

abbrev RawOp := Bool → Bool → Bool

def encodeBasis (B : List RawOp) : List Op := B.map encodeTruthTable

theorem encodeTruthTable_mem_encodeBasis_iff (f : RawOp) (B : List RawOp) :
    encodeTruthTable f ∈ encodeBasis B ↔ f ∈ B := by
  simp only [encodeBasis, List.mem_map]
  constructor
  · rintro ⟨g, hg, he⟩
    have hgf := encodeTruthTable_injective he
    simpa only [hgf] using hg
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem applyOp_mem_iff (h : Op) (B : List RawOp) :
    applyOp h ∈ B ↔ h ∈ encodeBasis B := by
  simpa only [encodeTruthTable_applyOp] using
    (encodeTruthTable_mem_encodeBasis_iff (applyOp h) B).symm

/-- Gates may carry arbitrary total binary Boolean functions directly. -/
inductive RawFormula (α : Type) where
  | leaf (symbol : α)
  | gate (f : RawOp) (left right : RawFormula α)

def RawFormula.eval {α : Type} (v : α → Bool) : RawFormula α → Bool
  | .leaf x => v x
  | .gate f a b => f (a.eval v) (b.eval v)

def RawFormula.size {α : Type} : RawFormula α → Nat
  | .leaf _ => 0
  | .gate _ a b => 1 + a.size + b.size

def RawFormula.depth {α : Type} : RawFormula α → Nat
  | .leaf _ => 0
  | .gate _ a b => 1 + max a.depth b.depth

def RawFormula.allowed {α : Type} (B : List RawOp) : RawFormula α → Prop
  | .leaf _ => True
  | .gate f a b => f ∈ B ∧ a.allowed B ∧ b.allowed B

def RawFormula.tautology {α : Type} (t : RawFormula α) : Prop :=
  ∀ v : α → Bool, t.eval v = true

/-- Replace each label by its truth table, keeping all gate occurrences and pins. -/
def RawFormula.encode {α : Type} : RawFormula α → Formula α
  | .leaf x => .leaf x
  | .gate f a b => .gate (encodeTruthTable f) a.encode b.encode

def Formula.decode {α : Type} : Formula α → RawFormula α
  | .leaf x => .leaf x
  | .gate h a b => .gate (applyOp h) a.decode b.decode

@[simp] theorem RawFormula.encode_eval {α : Type} (t : RawFormula α) (v : α → Bool) :
    t.encode.eval v = t.eval v := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [RawFormula.encode, Formula.eval, RawFormula.eval,
      applyOp_encodeTruthTable, ia, ib]

@[simp] theorem RawFormula.encode_size {α : Type} (t : RawFormula α) :
    t.encode.size = t.size := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [RawFormula.encode, Formula.size, RawFormula.size, ia, ib]

@[simp] theorem RawFormula.encode_depth {α : Type} (t : RawFormula α) :
    t.encode.depth = t.depth := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [RawFormula.encode, Formula.depth, RawFormula.depth, ia, ib]

@[simp] theorem RawFormula.encode_allowed {α : Type} (t : RawFormula α)
    (B : List RawOp) : t.encode.allowed (encodeBasis B) ↔ t.allowed B := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [RawFormula.encode, Formula.allowed, RawFormula.allowed,
      encodeTruthTable_mem_encodeBasis_iff, ia, ib]

@[simp] theorem RawFormula.encode_tautology {α : Type} (t : RawFormula α) :
    t.encode.tautology ↔ t.tautology := by
  simp only [Formula.tautology, RawFormula.tautology, RawFormula.encode_eval]

@[simp] theorem Formula.decode_eval {α : Type} (t : Formula α) (v : α → Bool) :
    t.decode.eval v = t.eval v := by
  induction t with
  | leaf x => rfl
  | gate h a b ia ib =>
    simp only [Formula.decode, RawFormula.eval, Formula.eval, ia, ib]

@[simp] theorem Formula.decode_size {α : Type} (t : Formula α) :
    t.decode.size = t.size := by
  induction t with
  | leaf x => rfl
  | gate h a b ia ib =>
    simp only [Formula.decode, RawFormula.size, Formula.size, ia, ib]

@[simp] theorem Formula.decode_depth {α : Type} (t : Formula α) :
    t.decode.depth = t.depth := by
  induction t with
  | leaf x => rfl
  | gate h a b ia ib =>
    simp only [Formula.decode, RawFormula.depth, Formula.depth, ia, ib]

@[simp] theorem Formula.decode_allowed {α : Type} (t : Formula α)
    (B : List RawOp) : t.decode.allowed B ↔ t.allowed (encodeBasis B) := by
  induction t with
  | leaf x => rfl
  | gate h a b ia ib =>
    simp only [Formula.decode, RawFormula.allowed, Formula.allowed,
      applyOp_mem_iff, ia, ib]

@[simp] theorem Formula.decode_tautology {α : Type} (t : Formula α) :
    t.decode.tautology ↔ t.tautology := by
  simp only [Formula.tautology, RawFormula.tautology, Formula.decode_eval]

@[simp] theorem RawFormula.decode_encode {α : Type} (t : RawFormula α) :
    t.encode.decode = t := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [RawFormula.encode, Formula.decode, binaryFunction_bijection.2, ia, ib]

@[simp] theorem Formula.encode_decode {α : Type} (t : Formula α) :
    t.decode.encode = t := by
  induction t with
  | leaf x => rfl
  | gate h a b ia ib =>
    simp only [Formula.decode, RawFormula.encode, encodeTruthTable_applyOp, ia, ib]

def ExactRawFormulaOver (α : Type) (B : List RawOp) (n : Nat) : Prop :=
  (∃ t : RawFormula α, t.allowed B ∧ t.tautology ∧ t.size = n) ∧
  ∀ t : RawFormula α, t.allowed B → t.tautology → n ≤ t.size

def ExactRawDepthOver (α : Type) (B : List RawOp) (n : Nat) : Prop :=
  (∃ t : RawFormula α, t.allowed B ∧ t.tautology ∧ t.depth = n) ∧
  ∀ t : RawFormula α, t.allowed B → t.tautology → n ≤ t.depth

theorem exactRawFormula_iff {α : Type} (B : List RawOp) (n : Nat) :
    ExactRawFormulaOver α B n ↔ ExactFormulaOver α (encodeBasis B) n := by
  constructor
  · rintro ⟨⟨t, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨t.encode, (t.encode_allowed B).2 ha, t.encode_tautology.2 ht,
        by simpa only [RawFormula.encode_size] using hc⟩
    · intro t ha ht
      have h := hl t.decode ((t.decode_allowed B).2 ha) (t.decode_tautology.2 ht)
      simpa only [Formula.decode_size] using h
  · rintro ⟨⟨t, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨t.decode, (t.decode_allowed B).2 ha, t.decode_tautology.2 ht,
        by simpa only [Formula.decode_size] using hc⟩
    · intro t ha ht
      have h := hl t.encode ((t.encode_allowed B).2 ha) (t.encode_tautology.2 ht)
      simpa only [RawFormula.encode_size] using h

theorem exactRawDepth_iff {α : Type} (B : List RawOp) (n : Nat) :
    ExactRawDepthOver α B n ↔ ExactDepthOver α (encodeBasis B) n := by
  constructor
  · rintro ⟨⟨t, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨t.encode, (t.encode_allowed B).2 ha, t.encode_tautology.2 ht,
        by simpa only [RawFormula.encode_depth] using hc⟩
    · intro t ha ht
      have h := hl t.decode ((t.decode_allowed B).2 ha) (t.decode_tautology.2 ht)
      simpa only [Formula.decode_depth] using h
  · rintro ⟨⟨t, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨t.decode, (t.decode_allowed B).2 ha, t.decode_tautology.2 ht,
        by simpa only [Formula.decode_depth] using hc⟩
    · intro t ha ht
      have h := hl t.encode ((t.encode_allowed B).2 ha) (t.encode_tautology.2 ht)
      simpa only [RawFormula.encode_depth] using h

end FIG22.Basis
