import BooleanSupport
import BasisDag
import Interface

/-!
# Cost-preserving representation of arbitrary binary-function-labelled DAGs

Only gate labels change under encoding. Allocated indices, ordered references,
the output reference, and distinct output ancestors are retained exactly.
Raw semantics are independently defined by unfolding arbitrary Boolean functions.
-/

namespace FIG22.Basis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure RawDag (α : Type) where
  allocated : Nat
  label : Fin allocated → RawOp
  pins : (i : Fin allocated) → Ref α i.val × Ref α i.val
  output : Ref α allocated

def RawDag.encode (c : RawDag α) : Dag α where
  allocated := c.allocated
  label i := encodeTruthTable (c.label i)
  pins := c.pins
  output := c.output

def Dag.decode (c : Dag α) : RawDag α where
  allocated := c.allocated
  label i := applyOp (c.label i)
  pins := c.pins
  output := c.output

def RawDag.unfold (c : RawDag α) {k : Nat} (hk : k ≤ c.allocated) :
    Ref α k → RawFormula α
  | .input x => .leaf x
  | .gate i =>
    let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
    .gate (c.label j) (c.unfold h (c.pins j).1) (c.unfold h (c.pins j).2)
termination_by k

def RawDag.ancestors (c : RawDag α) {k : Nat} (hk : k ≤ c.allocated) :
    Ref α k → List Nat
  | .input _ => []
  | .gate i =>
    let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
    (i.val :: c.ancestors h (c.pins j).1 ++ c.ancestors h (c.pins j).2).eraseDups
termination_by k

def RawDag.reachableCount (c : RawDag α) : Nat :=
  (c.ancestors (Nat.le_refl _) c.output).length

def RawDag.formula (c : RawDag α) : RawFormula α :=
  c.unfold (Nat.le_refl _) c.output

def RawDag.depth (c : RawDag α) : Nat := c.formula.depth

def RawDag.eval (c : RawDag α) (v : α → Bool) : Bool := c.formula.eval v

def RawDag.IsTrue (c : RawDag α) : Prop := ∀ v, c.eval v = true

def RawDag.Allowed (c : RawDag α) (B : List RawOp) : Prop :=
  ∀ i : Fin c.allocated, c.label i ∈ B

@[simp] theorem RawDag.decode_encode (c : RawDag α) : c.encode.decode = c := by
  cases c with
  | mk allocated label pins output =>
    simp only [RawDag.encode, Dag.decode]
    congr 1
    funext i
    exact binaryFunction_bijection.2 (label i)

@[simp] theorem Dag.encode_decode (c : Dag α) : c.decode.encode = c := by
  cases c with
  | mk allocated label pins output =>
    simp only [Dag.decode, RawDag.encode]
    congr 1
    funext i
    exact encodeTruthTable_applyOp (label i)

theorem RawDag.encode_unfold (c : RawDag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    c.encode.unfold hk r = (c.unfold hk r).encode := by
  cases r with
  | input x => simp only [RawDag.encode, Dag.unfold, RawDag.unfold, RawFormula.encode]
  | gate i =>
    simp only [Dag.unfold, RawDag.unfold, RawDag.encode, RawFormula.encode]
    congr 1
    · exact c.encode_unfold _ _
    · exact c.encode_unfold _ _
termination_by k

theorem RawDag.encode_ancestors (c : RawDag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    c.encode.ancestors hk r = c.ancestors hk r := by
  cases r with
  | input x => simp only [RawDag.encode, Dag.ancestors, RawDag.ancestors]
  | gate i =>
    simp only [Dag.ancestors, RawDag.ancestors, RawDag.encode]
    congr 3
    · exact c.encode_ancestors _ _
    · exact c.encode_ancestors _ _
termination_by k

@[simp] theorem RawDag.encode_formula (c : RawDag α) :
    c.encode.formula = c.formula.encode := c.encode_unfold _ _

@[simp] theorem RawDag.encode_eval (c : RawDag α) (v : α → Bool) :
    c.encode.eval v = c.eval v := by
  simp only [Dag.eval, RawDag.eval, RawDag.encode_formula, RawFormula.encode_eval]

@[simp] theorem RawDag.encode_depth (c : RawDag α) : c.encode.depth = c.depth := by
  simp only [Dag.depth, RawDag.depth, RawDag.encode_formula, RawFormula.encode_depth]

@[simp] theorem RawDag.encode_reachableCount (c : RawDag α) :
    c.encode.reachableCount = c.reachableCount := by
  exact congrArg List.length (c.encode_ancestors (Nat.le_refl _) c.output)

@[simp] theorem RawDag.encode_allowed (c : RawDag α) (B : List RawOp) :
    c.encode.Allowed (encodeBasis B) ↔ c.Allowed B := by
  simp only [Dag.Allowed, RawDag.Allowed, RawDag.encode,
    encodeTruthTable_mem_encodeBasis_iff]

@[simp] theorem RawDag.encode_isTrue (c : RawDag α) :
    c.encode.IsTrue ↔ c.IsTrue := by
  simp only [Dag.IsTrue, RawDag.IsTrue, RawDag.encode_eval]

theorem Dag.decode_unfold (c : Dag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    c.decode.unfold hk r = (c.unfold hk r).decode := by
  have h := congrArg Formula.decode (c.decode.encode_unfold hk r)
  simpa only [Dag.encode_decode, RawFormula.decode_encode] using h.symm

theorem Dag.decode_ancestors (c : Dag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    c.decode.ancestors hk r = c.ancestors hk r := by
  have h := c.decode.encode_ancestors hk r
  simpa only [Dag.encode_decode] using h.symm

@[simp] theorem Dag.decode_formula (c : Dag α) :
    c.decode.formula = c.formula.decode := c.decode_unfold _ _

@[simp] theorem Dag.decode_eval (c : Dag α) (v : α → Bool) :
    c.decode.eval v = c.eval v := by
  simp only [RawDag.eval, Dag.eval, Dag.decode_formula, Formula.decode_eval]

@[simp] theorem Dag.decode_depth (c : Dag α) : c.decode.depth = c.depth := by
  simp only [RawDag.depth, Dag.depth, Dag.decode_formula, Formula.decode_depth]

@[simp] theorem Dag.decode_reachableCount (c : Dag α) :
    c.decode.reachableCount = c.reachableCount := by
  exact congrArg List.length (c.decode_ancestors (Nat.le_refl _) c.output)

@[simp] theorem Dag.decode_allowed (c : Dag α) (B : List RawOp) :
    c.decode.Allowed B ↔ c.Allowed (encodeBasis B) := by
  simp only [RawDag.Allowed, Dag.Allowed, Dag.decode, applyOp_mem_iff]

@[simp] theorem Dag.decode_isTrue (c : Dag α) : c.decode.IsTrue ↔ c.IsTrue := by
  simp only [RawDag.IsTrue, Dag.IsTrue, Dag.decode_eval]

def ExactRawDagOver (α : Type) (B : List RawOp) (n : Nat) : Prop :=
  (∃ c : RawDag α, c.Allowed B ∧ c.IsTrue ∧ c.reachableCount = n) ∧
  ∀ c : RawDag α, c.Allowed B → c.IsTrue → n ≤ c.reachableCount

def ExactRawDagDepthOver (α : Type) (B : List RawOp) (n : Nat) : Prop :=
  (∃ c : RawDag α, c.Allowed B ∧ c.IsTrue ∧ c.depth = n) ∧
  ∀ c : RawDag α, c.Allowed B → c.IsTrue → n ≤ c.depth

theorem exactRawDag_iff {α : Type} (B : List RawOp) (n : Nat) :
    ExactRawDagOver α B n ↔ ExactDagOver α (encodeBasis B) n := by
  constructor
  · rintro ⟨⟨c, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨c.encode, (c.encode_allowed B).2 ha, c.encode_isTrue.2 ht,
        by simpa only [RawDag.encode_reachableCount] using hc⟩
    · intro c ha ht
      have h := hl c.decode ((c.decode_allowed B).2 ha) (c.decode_isTrue.2 ht)
      simpa only [Dag.decode_reachableCount] using h
  · rintro ⟨⟨c, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨c.decode, (c.decode_allowed B).2 ha, c.decode_isTrue.2 ht,
        by simpa only [Dag.decode_reachableCount] using hc⟩
    · intro c ha ht
      have h := hl c.encode ((c.encode_allowed B).2 ha) (c.encode_isTrue.2 ht)
      simpa only [RawDag.encode_reachableCount] using h

theorem exactRawDagDepth_iff {α : Type} (B : List RawOp) (n : Nat) :
    ExactRawDagDepthOver α B n ↔
      FIG22.Checked.ExactDagDepthOver α (encodeBasis B) n := by
  constructor
  · rintro ⟨⟨c, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨c.encode, (c.encode_allowed B).2 ha, c.encode_isTrue.2 ht,
        by simpa only [RawDag.encode_depth] using hc⟩
    · intro c ha ht
      have h := hl c.decode ((c.decode_allowed B).2 ha) (c.decode_isTrue.2 ht)
      simpa only [Dag.decode_depth] using h
  · rintro ⟨⟨c, ha, ht, hc⟩, hl⟩
    constructor
    · exact ⟨c.decode, (c.decode_allowed B).2 ha, c.decode_isTrue.2 ht,
        by simpa only [Dag.decode_depth] using hc⟩
    · intro c ha ht
      have h := hl c.encode ((c.encode_allowed B).2 ha) (c.encode_isTrue.2 ht)
      simpa only [RawDag.encode_depth] using h

theorem rawFormula_blocked_iff {α : Type} (B : List RawOp) :
    (∀ t : RawFormula α, t.allowed B → ¬t.tautology) ↔
      (∀ t : Formula α, t.allowed (encodeBasis B) → ¬t.tautology) := by
  constructor
  · intro h t ha ht
    exact h t.decode ((t.decode_allowed B).2 ha) (t.decode_tautology.2 ht)
  · intro h t ha ht
    exact h t.encode ((t.encode_allowed B).2 ha) (t.encode_tautology.2 ht)

theorem rawDag_blocked_iff {α : Type} (B : List RawOp) :
    (∀ c : RawDag α, c.Allowed B → ¬c.IsTrue) ↔
      (∀ c : Dag α, c.Allowed (encodeBasis B) → ¬c.IsTrue) := by
  constructor
  · intro h c ha ht
    exact h c.decode ((c.decode_allowed B).2 ha) (c.decode_isTrue.2 ht)
  · intro h c ha ht
    exact h c.encode ((c.encode_allowed B).2 ha) (c.encode_isTrue.2 ht)

end FIG22.Basis
