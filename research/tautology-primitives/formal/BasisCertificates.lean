import Std

/-!
# Kernel-checked certificates for the 136 FIG-22 singleton/pair bases

Operator numbers encode the ordered truth vector 00,01,10,11, with 00
as the most significant bit. All sixteen ordered binary functions are retained.
The four unary semantic values are FALSE, x, NOT x, TRUE. Gates have ordered
pins and cost one, including constant-valued and pin-ignoring operations.

Finite certificates are proposed by Python, but checked by `decide` in Lean's
kernel. The induction theorems below establish lower bounds for *all* finite
terms, and closure excludes TRUE without a syntactic search bound. No native
computation, additional axiom, or unchecked proof placeholder is used.
-/
namespace FIG22.Basis

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Op := Fin 16

inductive Unary where
  | zero | var | neg | one
  deriving DecidableEq, Repr

def evalAt (u : Unary) (x : Bool) : Bool :=
  match u with
  | .zero => false
  | .var => x
  | .neg => !x
  | .one => true

def ofBits : Bool → Bool → Unary
  | false, false => .zero
  | false, true => .var
  | true, false => .neg
  | true, true => .one

def applyOp (h : Op) (a b : Bool) : Bool :=
  (h.val / 2 ^ (3 - (2 * a.toNat + b.toNat))) % 2 == 1

def compose (h : Op) (u v : Unary) : Unary :=
  ofBits (applyOp h (evalAt u false) (evalAt v false))
    (applyOp h (evalAt u true) (evalAt v true))

inductive Term where
  | leaf
  | gate (h : Op) (left right : Term)
  deriving Repr

def Term.eval : Term → Unary
  | .leaf => .var
  | .gate h a b => compose h a.eval b.eval

def Term.size : Term → Nat
  | .leaf => 0
  | .gate _ a b => 1 + a.size + b.size

def Term.depth : Term → Nat
  | .leaf => 0
  | .gate _ a b => 1 + max a.depth b.depth

def Term.allowed (B : List Op) : Term → Prop
  | .leaf => True
  | .gate h a b => h ∈ B ∧ a.allowed B ∧ b.allowed B

instance (B : List Op) (t : Term) : Decidable (t.allowed B) := by
  induction t with
  | leaf => exact isTrue True.intro
  | gate h a b ia ib => unfold Term.allowed; infer_instance

/-- Explicit finite quantification avoids depending on an external finite-type library. -/
def CheckUnary (p : Unary → Prop) : Prop :=
  p .zero ∧ p .var ∧ p .neg ∧ p .one

instance (p : Unary → Prop) [DecidablePred p] : Decidable (CheckUnary p) :=
  inferInstanceAs (Decidable (p .zero ∧ p .var ∧ p .neg ∧ p .one))

theorem checkUnary_sound {p : Unary → Prop} (h : CheckUnary p) (u : Unary) : p u := by
  cases u with
  | zero => exact h.1
  | var => exact h.2.1
  | neg => exact h.2.2.1
  | one => exact h.2.2.2

def CheckOps (B : List Op) (p : Op → Prop) : Prop :=
  match B with
  | [] => True
  | h :: rest => p h ∧ CheckOps rest p

instance (B : List Op) (p : Op → Prop) [DecidablePred p] :
    Decidable (CheckOps B p) := by
  induction B with
  | nil => exact isTrue True.intro
  | cons h rest ih => unfold CheckOps; infer_instance

theorem checkOps_sound {B : List Op} {p : Op → Prop}
    (c : CheckOps B p) {h : Op} (hm : h ∈ B) : p h := by
  induction B with
  | nil => simp at hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with heq | hrest
    · subst h; exact c.1
    · exact ih c.2 hrest

def FormulaValid (B : List Op) (w : Unary → Nat) : Prop :=
  w .var = 0 ∧ CheckOps B (fun h => CheckUnary (fun u => CheckUnary (fun v =>
    w (compose h u v) ≤ 1 + w u + w v)))

def DepthValid (B : List Op) (w : Unary → Nat) : Prop :=
  w .var = 0 ∧ CheckOps B (fun h => CheckUnary (fun u => CheckUnary (fun v =>
    w (compose h u v) ≤ 1 + max (w u) (w v))))

def ClosureValid (B : List Op) (s : Unary → Bool) : Prop :=
  s .var = true ∧ CheckOps B (fun h => CheckUnary (fun u => CheckUnary (fun v =>
    s u = true → s v = true → s (compose h u v) = true)))

instance (B : List Op) (w : Unary → Nat) : Decidable (FormulaValid B w) := by
  unfold FormulaValid; infer_instance
instance (B : List Op) (w : Unary → Nat) : Decidable (DepthValid B w) := by
  unfold DepthValid; infer_instance
instance (B : List Op) (s : Unary → Bool) : Decidable (ClosureValid B s) := by
  unfold ClosureValid; infer_instance

/-- A finite Bellman inequality bounds every finite formula, without a size cutoff. -/
theorem formula_lower {B : List Op} {w : Unary → Nat}
    (c : FormulaValid B w) (t : Term) (ht : t.allowed B) : w t.eval ≤ t.size := by
  induction t with
  | leaf => simp [Term.eval, Term.size, c.1]
  | gate h a b ia ib =>
    have step := checkUnary_sound (checkUnary_sound (checkOps_sound c.2 ht.1) a.eval) b.eval
    have ha := ia ht.2.1
    have hb := ib ht.2.2
    exact Nat.le_trans step (by
      simpa [Term.size] using Nat.add_le_add (Nat.add_le_add_left ha 1) hb)

/-- The max recurrence bounds depth for every finite formula. -/
theorem depth_lower {B : List Op} {w : Unary → Nat}
    (c : DepthValid B w) (t : Term) (ht : t.allowed B) : w t.eval ≤ t.depth := by
  induction t with
  | leaf => simp [Term.eval, Term.depth, c.1]
  | gate h a b ia ib =>
    have step := checkUnary_sound (checkUnary_sound (checkOps_sound c.2 ht.1) a.eval) b.eval
    have ha := ia ht.2.1
    have hb := ib ht.2.2
    exact Nat.le_trans step (Nat.add_le_add_left ((Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩)) 1)

/-- A closed set containing x contains the evaluation of every finite term. -/
theorem closure_sound {B : List Op} {s : Unary → Bool}
    (c : ClosureValid B s) (t : Term) (ht : t.allowed B) : s t.eval = true := by
  induction t with
  | leaf => exact c.1
  | gate h a b ia ib =>
    exact checkUnary_sound (checkUnary_sound (checkOps_sound c.2 ht.1) a.eval) b.eval
      (ia ht.2.1) (ib ht.2.2)

def ExactFormula (B : List Op) (n : Nat) : Prop :=
  (∃ t : Term, t.allowed B ∧ t.eval = .one ∧ t.size = n) ∧
  ∀ t : Term, t.allowed B → t.eval = .one → n ≤ t.size

def ExactDepth (B : List Op) (n : Nat) : Prop :=
  (∃ t : Term, t.allowed B ∧ t.eval = .one ∧ t.depth = n) ∧
  ∀ t : Term, t.allowed B → t.eval = .one → n ≤ t.depth

def Blocked (B : List Op) : Prop :=
  ∀ t : Term, t.allowed B → t.eval ≠ .one

/-! ## Cost-preserving substitution for arbitrary variable-labelled formulas -/

inductive Formula (α : Type) where
  | leaf (symbol : α)
  | gate (h : Op) (left right : Formula α)

def Formula.eval {α : Type} (v : α → Bool) : Formula α → Bool
  | .leaf x => v x
  | .gate h a b => applyOp h (a.eval v) (b.eval v)

def Formula.diagonal {α : Type} : Formula α → Term
  | .leaf _ => .leaf
  | .gate h a b => .gate h a.diagonal b.diagonal

def Formula.size {α : Type} : Formula α → Nat
  | .leaf _ => 0
  | .gate _ a b => 1 + a.size + b.size

def Formula.depth {α : Type} : Formula α → Nat
  | .leaf _ => 0
  | .gate _ a b => 1 + max a.depth b.depth

def Formula.allowed {α : Type} (B : List Op) : Formula α → Prop
  | .leaf _ => True
  | .gate h a b => h ∈ B ∧ a.allowed B ∧ b.allowed B

def Formula.tautology {α : Type} (t : Formula α) : Prop :=
  ∀ v : α → Bool, t.eval v = true

 theorem evalAt_ofBits (a b x : Bool) :
    evalAt (ofBits a b) x = if x then b else a := by
  cases a <;> cases b <;> cases x <;> rfl

 theorem evalAt_compose (h : Op) (u v : Unary) (x : Bool) :
    evalAt (compose h u v) x = applyOp h (evalAt u x) (evalAt v x) := by
  cases x <;> simp [compose, evalAt_ofBits]

 theorem Formula.diagonal_eval {α : Type} (t : Formula α) (x : Bool) :
    evalAt t.diagonal.eval x = t.eval (fun _ => x) := by
  induction t with
  | leaf a => rfl
  | gate h a b ia ib =>
    simp only [Formula.diagonal, Term.eval, Formula.eval, evalAt_compose, ia, ib]

 theorem Formula.diagonal_size {α : Type} (t : Formula α) :
    t.diagonal.size = t.size := by
  induction t with
  | leaf a => rfl
  | gate h a b ia ib => simp only [Formula.diagonal, Term.size, Formula.size, ia, ib]

 theorem Formula.diagonal_depth {α : Type} (t : Formula α) :
    t.diagonal.depth = t.depth := by
  induction t with
  | leaf a => rfl
  | gate h a b ia ib => simp only [Formula.diagonal, Term.depth, Formula.depth, ia, ib]

 theorem Formula.diagonal_allowed {α : Type} {B : List Op} (t : Formula α)
    (ht : t.allowed B) : t.diagonal.allowed B := by
  induction t with
  | leaf a => trivial
  | gate h a b ia ib => exact ⟨ht.1, ia ht.2.1, ib ht.2.2⟩

 theorem Formula.tautology_diagonal {α : Type} (t : Formula α)
    (ht : t.tautology) : t.diagonal.eval = .one := by
  have h0 := t.diagonal_eval false
  have h1 := t.diagonal_eval true
  rw [ht (fun _ => false)] at h0
  rw [ht (fun _ => true)] at h1
  cases he : t.diagonal.eval <;> simp_all [evalAt]

 def Term.label {α : Type} (x : α) : Term → Formula α
  | .leaf => .leaf x
  | .gate h a b => .gate h (a.label x) (b.label x)

 theorem Term.label_eval {α : Type} (x : α) (t : Term) (v : α → Bool) :
    (t.label x).eval v = evalAt t.eval (v x) := by
  induction t with
  | leaf => rfl
  | gate h a b ia ib =>
    simp only [Term.label, Formula.eval, Term.eval, evalAt_compose, ia, ib]

 theorem Term.label_size {α : Type} (x : α) (t : Term) :
    (t.label x).size = t.size := by
  induction t with
  | leaf => rfl
  | gate h a b ia ib => simp only [Term.label, Formula.size, Term.size, ia, ib]

 theorem Term.label_depth {α : Type} (x : α) (t : Term) :
    (t.label x).depth = t.depth := by
  induction t with
  | leaf => rfl
  | gate h a b ia ib => simp only [Term.label, Formula.depth, Term.depth, ia, ib]

 theorem Term.label_allowed {α : Type} (x : α) {B : List Op} (t : Term)
    (ht : t.allowed B) : (t.label x).allowed B := by
  induction t with
  | leaf => trivial
  | gate h a b ia ib => exact ⟨ht.1, ia ht.2.1, ib ht.2.2⟩

 def ExactFormulaOver (α : Type) (B : List Op) (n : Nat) : Prop :=
  (∃ t : Formula α, t.allowed B ∧ t.tautology ∧ t.size = n) ∧
  ∀ t : Formula α, t.allowed B → t.tautology → n ≤ t.size

 def ExactDepthOver (α : Type) (B : List Op) (n : Nat) : Prop :=
  (∃ t : Formula α, t.allowed B ∧ t.tautology ∧ t.depth = n) ∧
  ∀ t : Formula α, t.allowed B → t.tautology → n ≤ t.depth

 theorem exactFormula_over {α : Type} (x : α) {B : List Op} {n : Nat}
    (h : ExactFormula B n) : ExactFormulaOver α B n := by
  constructor
  · rcases h.1 with ⟨t, ha, he, hc⟩
    refine ⟨t.label x, t.label_allowed x ha, ?_, ?_⟩
    · intro v; rw [Term.label_eval, he]; rfl
    · rw [Term.label_size, hc]
  · intro t ha ht
    have hl := h.2 t.diagonal (t.diagonal_allowed ha) (t.tautology_diagonal ht)
    simpa only [Formula.diagonal_size] using hl

 theorem exactDepth_over {α : Type} (x : α) {B : List Op} {n : Nat}
    (h : ExactDepth B n) : ExactDepthOver α B n := by
  constructor
  · rcases h.1 with ⟨t, ha, he, hc⟩
    refine ⟨t.label x, t.label_allowed x ha, ?_, ?_⟩
    · intro v; rw [Term.label_eval, he]; rfl
    · rw [Term.label_depth, hc]
  · intro t ha ht
    have hl := h.2 t.diagonal (t.diagonal_allowed ha) (t.tautology_diagonal ht)
    simpa only [Formula.diagonal_depth] using hl

 theorem blocked_over {α : Type} {B : List Op} (h : Blocked B)
    (t : Formula α) (ha : t.allowed B) : ¬t.tautology := by
  intro ht
  exact h t.diagonal (t.diagonal_allowed ha) (t.tautology_diagonal ht)

structure Row where
  basis : List Op
  formulaWeight : Unary → Nat
  depthWeight : Unary → Nat
  reachable : Unary → Bool
  generates : Bool
  formulaCost : Nat
  depthCost : Nat
  formulaWitness : Term
  depthWitness : Term

def OutcomeValid (r : Row) : Prop :=
  if r.generates then
    r.formulaWeight .one = r.formulaCost ∧
    r.depthWeight .one = r.depthCost ∧
    r.formulaWitness.allowed r.basis ∧ r.formulaWitness.eval = .one ∧
    r.formulaWitness.size = r.formulaCost ∧
    r.depthWitness.allowed r.basis ∧ r.depthWitness.eval = .one ∧
    r.depthWitness.depth = r.depthCost
  else r.reachable .one = false

instance (r : Row) : Decidable (OutcomeValid r) := by
  unfold OutcomeValid; infer_instance

def Valid (r : Row) : Prop :=
  FormulaValid r.basis r.formulaWeight ∧ DepthValid r.basis r.depthWeight ∧
    ClosureValid r.basis r.reachable ∧ OutcomeValid r

instance (r : Row) : Decidable (Valid r) := by unfold Valid; infer_instance

/-- Every accepted generating row proves two unbounded exact minimum theorems. -/
theorem valid_generating (r : Row) (c : Valid r) (hg : r.generates = true) :
    ExactFormula r.basis r.formulaCost ∧ ExactDepth r.basis r.depthCost := by
  have o := c.2.2.2
  simp only [OutcomeValid, hg, ↓reduceIte] at o
  rcases o with ⟨hf, hd, hfa, hfe, hfc, hda, hde, hdc⟩
  constructor
  · constructor
    · exact ⟨r.formulaWitness, hfa, hfe, hfc⟩
    · intro t ht he
      have h := formula_lower c.1 t ht
      simpa only [he, hf] using h
  · constructor
    · exact ⟨r.depthWitness, hda, hde, hdc⟩
    · intro t ht he
      have h := depth_lower c.2.1 t ht
      simpa only [he, hd] using h

/-- Every accepted blocked row excludes TRUE for all finite terms. -/
theorem valid_blocked (r : Row) (c : Valid r) (hg : r.generates = false) :
    Blocked r.basis := by
  have o := c.2.2.2
  simp only [OutcomeValid, hg, Bool.false_eq_true, ↓reduceIte] at o
  intro t ht he
  have h := closure_sound c.2.2.1 t ht
  rw [he, o] at h
  contradiction

-- 0: FALSE; evidence basis_ids=[0]
def row000 : Row where
  basis := [0]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row000_valid : Valid row000 := by decide
theorem row000_blocked : Blocked row000.basis :=
  valid_blocked row000 row000_valid rfl

-- 1: AND; evidence basis_ids=[1]
def row001 : Row where
  basis := [1]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row001_valid : Valid row001 := by decide
theorem row001_blocked : Blocked row001.basis :=
  valid_blocked row001 row001_valid rfl

-- 2: X_AND_NOT_Y; evidence basis_ids=[2]
def row002 : Row where
  basis := [2]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row002_valid : Valid row002 := by decide
theorem row002_blocked : Blocked row002.basis :=
  valid_blocked row002 row002_valid rfl

-- 3: X; evidence basis_ids=[3]
def row003 : Row where
  basis := [3]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row003_valid : Valid row003 := by decide
theorem row003_blocked : Blocked row003.basis :=
  valid_blocked row003 row003_valid rfl

-- 4: NOT_X_AND_Y; evidence basis_ids=[4]
def row004 : Row where
  basis := [4]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row004_valid : Valid row004 := by decide
theorem row004_blocked : Blocked row004.basis :=
  valid_blocked row004 row004_valid rfl

-- 5: Y; evidence basis_ids=[5]
def row005 : Row where
  basis := [5]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row005_valid : Valid row005 := by decide
theorem row005_blocked : Blocked row005.basis :=
  valid_blocked row005 row005_valid rfl

-- 6: XOR; evidence basis_ids=[6]
def row006 : Row where
  basis := [6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row006_valid : Valid row006 := by decide
theorem row006_blocked : Blocked row006.basis :=
  valid_blocked row006 row006_valid rfl

-- 7: OR; evidence basis_ids=[7]
def row007 : Row where
  basis := [7]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row007_valid : Valid row007 := by decide
theorem row007_blocked : Blocked row007.basis :=
  valid_blocked row007 row007_valid rfl

-- 8: NOR; evidence basis_ids=[8]
def row008 : Row where
  basis := [8]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 5
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 5
  depthCost := 3
  formulaWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
  depthWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
theorem row008_valid : Valid row008 := by decide
theorem row008_exact : ExactFormula row008.basis row008.formulaCost ∧
    ExactDepth row008.basis row008.depthCost :=
  valid_generating row008 row008_valid rfl

-- 9: XNOR; evidence basis_ids=[9]
def row009 : Row where
  basis := [9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row009_valid : Valid row009 := by decide
theorem row009_exact : ExactFormula row009.basis row009.formulaCost ∧
    ExactDepth row009.basis row009.depthCost :=
  valid_generating row009 row009_valid rfl

-- 10: NOT_Y; evidence basis_ids=[10]
def row010 : Row where
  basis := [10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row010_valid : Valid row010 := by decide
theorem row010_blocked : Blocked row010.basis :=
  valid_blocked row010 row010_valid rfl

-- 11: Y_IMPLIES_X; evidence basis_ids=[11]
def row011 : Row where
  basis := [11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row011_valid : Valid row011 := by decide
theorem row011_exact : ExactFormula row011.basis row011.formulaCost ∧
    ExactDepth row011.basis row011.depthCost :=
  valid_generating row011 row011_valid rfl

-- 12: NOT_X; evidence basis_ids=[12]
def row012 : Row where
  basis := [12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row012_valid : Valid row012 := by decide
theorem row012_blocked : Blocked row012.basis :=
  valid_blocked row012 row012_valid rfl

-- 13: X_IMPLIES_Y; evidence basis_ids=[13]
def row013 : Row where
  basis := [13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row013_valid : Valid row013 := by decide
theorem row013_exact : ExactFormula row013.basis row013.formulaCost ∧
    ExactDepth row013.basis row013.depthCost :=
  valid_generating row013 row013_valid rfl

-- 14: NAND; evidence basis_ids=[14]
def row014 : Row where
  basis := [14]
  formulaWeight := fun | .zero => 5 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
theorem row014_valid : Valid row014 := by decide
theorem row014_exact : ExactFormula row014.basis row014.formulaCost ∧
    ExactDepth row014.basis row014.depthCost :=
  valid_generating row014 row014_valid rfl

-- 15: TRUE; evidence basis_ids=[15]
def row015 : Row where
  basis := [15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row015_valid : Valid row015 := by decide
theorem row015_exact : ExactFormula row015.basis row015.formulaCost ∧
    ExactDepth row015.basis row015.depthCost :=
  valid_generating row015 row015_valid rfl

-- 16: FALSE, AND; evidence basis_ids=[0, 1]
def row016 : Row where
  basis := [0, 1]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row016_valid : Valid row016 := by decide
theorem row016_blocked : Blocked row016.basis :=
  valid_blocked row016 row016_valid rfl

-- 17: FALSE, X_AND_NOT_Y; evidence basis_ids=[0, 2]
def row017 : Row where
  basis := [0, 2]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row017_valid : Valid row017 := by decide
theorem row017_blocked : Blocked row017.basis :=
  valid_blocked row017 row017_valid rfl

-- 18: FALSE, X; evidence basis_ids=[0, 3]
def row018 : Row where
  basis := [0, 3]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row018_valid : Valid row018 := by decide
theorem row018_blocked : Blocked row018.basis :=
  valid_blocked row018 row018_valid rfl

-- 19: FALSE, NOT_X_AND_Y; evidence basis_ids=[0, 4]
def row019 : Row where
  basis := [0, 4]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row019_valid : Valid row019 := by decide
theorem row019_blocked : Blocked row019.basis :=
  valid_blocked row019 row019_valid rfl

-- 20: FALSE, Y; evidence basis_ids=[0, 5]
def row020 : Row where
  basis := [0, 5]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row020_valid : Valid row020 := by decide
theorem row020_blocked : Blocked row020.basis :=
  valid_blocked row020 row020_valid rfl

-- 21: FALSE, XOR; evidence basis_ids=[0, 6]
def row021 : Row where
  basis := [0, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row021_valid : Valid row021 := by decide
theorem row021_blocked : Blocked row021.basis :=
  valid_blocked row021 row021_valid rfl

-- 22: FALSE, OR; evidence basis_ids=[0, 7]
def row022 : Row where
  basis := [0, 7]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row022_valid : Valid row022 := by decide
theorem row022_blocked : Blocked row022.basis :=
  valid_blocked row022 row022_valid rfl

-- 23: FALSE, NOR; evidence basis_ids=[0, 8]
def row023 : Row where
  basis := [0, 8]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 2
  formulaWitness := (.gate 8 (.gate 0 .leaf .leaf) (.gate 0 .leaf .leaf))
  depthWitness := (.gate 8 (.gate 0 .leaf .leaf) (.gate 0 .leaf .leaf))
theorem row023_valid : Valid row023 := by decide
theorem row023_exact : ExactFormula row023.basis row023.formulaCost ∧
    ExactDepth row023.basis row023.depthCost :=
  valid_generating row023 row023_valid rfl

-- 24: FALSE, XNOR; evidence basis_ids=[0, 9]
def row024 : Row where
  basis := [0, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row024_valid : Valid row024 := by decide
theorem row024_exact : ExactFormula row024.basis row024.formulaCost ∧
    ExactDepth row024.basis row024.depthCost :=
  valid_generating row024 row024_valid rfl

-- 25: FALSE, NOT_Y; evidence basis_ids=[0, 10]
def row025 : Row where
  basis := [0, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 10 .leaf (.gate 0 .leaf .leaf))
  depthWitness := (.gate 10 (.gate 0 .leaf .leaf) (.gate 0 .leaf .leaf))
theorem row025_valid : Valid row025 := by decide
theorem row025_exact : ExactFormula row025.basis row025.formulaCost ∧
    ExactDepth row025.basis row025.depthCost :=
  valid_generating row025 row025_valid rfl

-- 26: FALSE, Y_IMPLIES_X; evidence basis_ids=[0, 11]
def row026 : Row where
  basis := [0, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row026_valid : Valid row026 := by decide
theorem row026_exact : ExactFormula row026.basis row026.formulaCost ∧
    ExactDepth row026.basis row026.depthCost :=
  valid_generating row026 row026_valid rfl

-- 27: FALSE, NOT_X; evidence basis_ids=[0, 12]
def row027 : Row where
  basis := [0, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 12 (.gate 0 .leaf .leaf) .leaf)
  depthWitness := (.gate 12 (.gate 0 .leaf .leaf) (.gate 0 .leaf .leaf))
theorem row027_valid : Valid row027 := by decide
theorem row027_exact : ExactFormula row027.basis row027.formulaCost ∧
    ExactDepth row027.basis row027.depthCost :=
  valid_generating row027 row027_valid rfl

-- 28: FALSE, X_IMPLIES_Y; evidence basis_ids=[0, 13]
def row028 : Row where
  basis := [0, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row028_valid : Valid row028 := by decide
theorem row028_exact : ExactFormula row028.basis row028.formulaCost ∧
    ExactDepth row028.basis row028.depthCost :=
  valid_generating row028 row028_valid rfl

-- 29: FALSE, NAND; evidence basis_ids=[0, 14]
def row029 : Row where
  basis := [0, 14]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 (.gate 0 .leaf .leaf) .leaf)
  depthWitness := (.gate 14 (.gate 0 .leaf .leaf) (.gate 0 .leaf .leaf))
theorem row029_valid : Valid row029 := by decide
theorem row029_exact : ExactFormula row029.basis row029.formulaCost ∧
    ExactDepth row029.basis row029.depthCost :=
  valid_generating row029 row029_valid rfl

-- 30: FALSE, TRUE; evidence basis_ids=[0, 15]
def row030 : Row where
  basis := [0, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row030_valid : Valid row030 := by decide
theorem row030_exact : ExactFormula row030.basis row030.formulaCost ∧
    ExactDepth row030.basis row030.depthCost :=
  valid_generating row030 row030_valid rfl

-- 31: AND, X_AND_NOT_Y; evidence basis_ids=[1, 2]
def row031 : Row where
  basis := [1, 2]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row031_valid : Valid row031 := by decide
theorem row031_blocked : Blocked row031.basis :=
  valid_blocked row031 row031_valid rfl

-- 32: AND, X; evidence basis_ids=[1, 3]
def row032 : Row where
  basis := [1, 3]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row032_valid : Valid row032 := by decide
theorem row032_blocked : Blocked row032.basis :=
  valid_blocked row032 row032_valid rfl

-- 33: AND, NOT_X_AND_Y; evidence basis_ids=[1, 4]
def row033 : Row where
  basis := [1, 4]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row033_valid : Valid row033 := by decide
theorem row033_blocked : Blocked row033.basis :=
  valid_blocked row033 row033_valid rfl

-- 34: AND, Y; evidence basis_ids=[1, 5]
def row034 : Row where
  basis := [1, 5]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row034_valid : Valid row034 := by decide
theorem row034_blocked : Blocked row034.basis :=
  valid_blocked row034 row034_valid rfl

-- 35: AND, XOR; evidence basis_ids=[1, 6]
def row035 : Row where
  basis := [1, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row035_valid : Valid row035 := by decide
theorem row035_blocked : Blocked row035.basis :=
  valid_blocked row035 row035_valid rfl

-- 36: AND, OR; evidence basis_ids=[1, 7]
def row036 : Row where
  basis := [1, 7]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row036_valid : Valid row036 := by decide
theorem row036_blocked : Blocked row036.basis :=
  valid_blocked row036 row036_valid rfl

-- 37: AND, NOR; evidence basis_ids=[1, 8]
def row037 : Row where
  basis := [1, 8]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 5
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 5
  depthCost := 3
  formulaWitness := (.gate 8 (.gate 1 .leaf (.gate 8 .leaf .leaf)) (.gate 1 .leaf (.gate 8 .leaf .leaf)))
  depthWitness := (.gate 8 (.gate 1 .leaf (.gate 8 .leaf .leaf)) (.gate 1 .leaf (.gate 8 .leaf .leaf)))
theorem row037_valid : Valid row037 := by decide
theorem row037_exact : ExactFormula row037.basis row037.formulaCost ∧
    ExactDepth row037.basis row037.depthCost :=
  valid_generating row037 row037_valid rfl

-- 38: AND, XNOR; evidence basis_ids=[1, 9]
def row038 : Row where
  basis := [1, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row038_valid : Valid row038 := by decide
theorem row038_exact : ExactFormula row038.basis row038.formulaCost ∧
    ExactDepth row038.basis row038.depthCost :=
  valid_generating row038 row038_valid rfl

-- 39: AND, NOT_Y; evidence basis_ids=[1, 10]
def row039 : Row where
  basis := [1, 10]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 3
  formulaWitness := (.gate 10 .leaf (.gate 1 .leaf (.gate 10 .leaf .leaf)))
  depthWitness := (.gate 10 (.gate 1 .leaf (.gate 10 .leaf .leaf)) (.gate 1 .leaf (.gate 10 .leaf .leaf)))
theorem row039_valid : Valid row039 := by decide
theorem row039_exact : ExactFormula row039.basis row039.formulaCost ∧
    ExactDepth row039.basis row039.depthCost :=
  valid_generating row039 row039_valid rfl

-- 40: AND, Y_IMPLIES_X; evidence basis_ids=[1, 11]
def row040 : Row where
  basis := [1, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row040_valid : Valid row040 := by decide
theorem row040_exact : ExactFormula row040.basis row040.formulaCost ∧
    ExactDepth row040.basis row040.depthCost :=
  valid_generating row040 row040_valid rfl

-- 41: AND, NOT_X; evidence basis_ids=[1, 12]
def row041 : Row where
  basis := [1, 12]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 3
  formulaWitness := (.gate 12 (.gate 1 .leaf (.gate 12 .leaf .leaf)) .leaf)
  depthWitness := (.gate 12 (.gate 1 .leaf (.gate 12 .leaf .leaf)) (.gate 1 .leaf (.gate 12 .leaf .leaf)))
theorem row041_valid : Valid row041 := by decide
theorem row041_exact : ExactFormula row041.basis row041.formulaCost ∧
    ExactDepth row041.basis row041.depthCost :=
  valid_generating row041 row041_valid rfl

-- 42: AND, X_IMPLIES_Y; evidence basis_ids=[1, 13]
def row042 : Row where
  basis := [1, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row042_valid : Valid row042 := by decide
theorem row042_exact : ExactFormula row042.basis row042.formulaCost ∧
    ExactDepth row042.basis row042.depthCost :=
  valid_generating row042 row042_valid rfl

-- 43: AND, NAND; evidence basis_ids=[1, 14]
def row043 : Row where
  basis := [1, 14]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
theorem row043_valid : Valid row043 := by decide
theorem row043_exact : ExactFormula row043.basis row043.formulaCost ∧
    ExactDepth row043.basis row043.depthCost :=
  valid_generating row043 row043_valid rfl

-- 44: AND, TRUE; evidence basis_ids=[1, 15]
def row044 : Row where
  basis := [1, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row044_valid : Valid row044 := by decide
theorem row044_exact : ExactFormula row044.basis row044.formulaCost ∧
    ExactDepth row044.basis row044.depthCost :=
  valid_generating row044 row044_valid rfl

-- 45: X_AND_NOT_Y, X; evidence basis_ids=[2, 3]
def row045 : Row where
  basis := [2, 3]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row045_valid : Valid row045 := by decide
theorem row045_blocked : Blocked row045.basis :=
  valid_blocked row045 row045_valid rfl

-- 46: X_AND_NOT_Y, NOT_X_AND_Y; evidence basis_ids=[2, 4]
def row046 : Row where
  basis := [2, 4]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row046_valid : Valid row046 := by decide
theorem row046_blocked : Blocked row046.basis :=
  valid_blocked row046 row046_valid rfl

-- 47: X_AND_NOT_Y, Y; evidence basis_ids=[2, 5]
def row047 : Row where
  basis := [2, 5]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row047_valid : Valid row047 := by decide
theorem row047_blocked : Blocked row047.basis :=
  valid_blocked row047 row047_valid rfl

-- 48: X_AND_NOT_Y, XOR; evidence basis_ids=[2, 6]
def row048 : Row where
  basis := [2, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row048_valid : Valid row048 := by decide
theorem row048_blocked : Blocked row048.basis :=
  valid_blocked row048 row048_valid rfl

-- 49: X_AND_NOT_Y, OR; evidence basis_ids=[2, 7]
def row049 : Row where
  basis := [2, 7]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row049_valid : Valid row049 := by decide
theorem row049_blocked : Blocked row049.basis :=
  valid_blocked row049 row049_valid rfl

-- 50: X_AND_NOT_Y, NOR; evidence basis_ids=[2, 8]
def row050 : Row where
  basis := [2, 8]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 2
  formulaWitness := (.gate 8 (.gate 2 .leaf .leaf) (.gate 2 .leaf .leaf))
  depthWitness := (.gate 8 (.gate 2 .leaf .leaf) (.gate 2 .leaf .leaf))
theorem row050_valid : Valid row050 := by decide
theorem row050_exact : ExactFormula row050.basis row050.formulaCost ∧
    ExactDepth row050.basis row050.depthCost :=
  valid_generating row050 row050_valid rfl

-- 51: X_AND_NOT_Y, XNOR; evidence basis_ids=[2, 9]
def row051 : Row where
  basis := [2, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row051_valid : Valid row051 := by decide
theorem row051_exact : ExactFormula row051.basis row051.formulaCost ∧
    ExactDepth row051.basis row051.depthCost :=
  valid_generating row051 row051_valid rfl

-- 52: X_AND_NOT_Y, NOT_Y; evidence basis_ids=[2, 10]
def row052 : Row where
  basis := [2, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 10 .leaf (.gate 2 .leaf .leaf))
  depthWitness := (.gate 10 (.gate 2 .leaf .leaf) (.gate 2 .leaf .leaf))
theorem row052_valid : Valid row052 := by decide
theorem row052_exact : ExactFormula row052.basis row052.formulaCost ∧
    ExactDepth row052.basis row052.depthCost :=
  valid_generating row052 row052_valid rfl

-- 53: X_AND_NOT_Y, Y_IMPLIES_X; evidence basis_ids=[2, 11]
def row053 : Row where
  basis := [2, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row053_valid : Valid row053 := by decide
theorem row053_exact : ExactFormula row053.basis row053.formulaCost ∧
    ExactDepth row053.basis row053.depthCost :=
  valid_generating row053 row053_valid rfl

-- 54: X_AND_NOT_Y, NOT_X; evidence basis_ids=[2, 12]
def row054 : Row where
  basis := [2, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 12 (.gate 2 .leaf .leaf) .leaf)
  depthWitness := (.gate 12 (.gate 2 .leaf .leaf) (.gate 2 .leaf .leaf))
theorem row054_valid : Valid row054 := by decide
theorem row054_exact : ExactFormula row054.basis row054.formulaCost ∧
    ExactDepth row054.basis row054.depthCost :=
  valid_generating row054 row054_valid rfl

-- 55: X_AND_NOT_Y, X_IMPLIES_Y; evidence basis_ids=[2, 13]
def row055 : Row where
  basis := [2, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row055_valid : Valid row055 := by decide
theorem row055_exact : ExactFormula row055.basis row055.formulaCost ∧
    ExactDepth row055.basis row055.depthCost :=
  valid_generating row055 row055_valid rfl

-- 56: X_AND_NOT_Y, NAND; evidence basis_ids=[2, 14]
def row056 : Row where
  basis := [2, 14]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 (.gate 2 .leaf .leaf) .leaf)
  depthWitness := (.gate 14 (.gate 2 .leaf .leaf) (.gate 2 .leaf .leaf))
theorem row056_valid : Valid row056 := by decide
theorem row056_exact : ExactFormula row056.basis row056.formulaCost ∧
    ExactDepth row056.basis row056.depthCost :=
  valid_generating row056 row056_valid rfl

-- 57: X_AND_NOT_Y, TRUE; evidence basis_ids=[2, 15]
def row057 : Row where
  basis := [2, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row057_valid : Valid row057 := by decide
theorem row057_exact : ExactFormula row057.basis row057.formulaCost ∧
    ExactDepth row057.basis row057.depthCost :=
  valid_generating row057 row057_valid rfl

-- 58: X, NOT_X_AND_Y; evidence basis_ids=[3, 4]
def row058 : Row where
  basis := [3, 4]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row058_valid : Valid row058 := by decide
theorem row058_blocked : Blocked row058.basis :=
  valid_blocked row058 row058_valid rfl

-- 59: X, Y; evidence basis_ids=[3, 5]
def row059 : Row where
  basis := [3, 5]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row059_valid : Valid row059 := by decide
theorem row059_blocked : Blocked row059.basis :=
  valid_blocked row059 row059_valid rfl

-- 60: X, XOR; evidence basis_ids=[3, 6]
def row060 : Row where
  basis := [3, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row060_valid : Valid row060 := by decide
theorem row060_blocked : Blocked row060.basis :=
  valid_blocked row060 row060_valid rfl

-- 61: X, OR; evidence basis_ids=[3, 7]
def row061 : Row where
  basis := [3, 7]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row061_valid : Valid row061 := by decide
theorem row061_blocked : Blocked row061.basis :=
  valid_blocked row061 row061_valid rfl

-- 62: X, NOR; evidence basis_ids=[3, 8]
def row062 : Row where
  basis := [3, 8]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 5
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 5
  depthCost := 3
  formulaWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
  depthWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
theorem row062_valid : Valid row062 := by decide
theorem row062_exact : ExactFormula row062.basis row062.formulaCost ∧
    ExactDepth row062.basis row062.depthCost :=
  valid_generating row062 row062_valid rfl

-- 63: X, XNOR; evidence basis_ids=[3, 9]
def row063 : Row where
  basis := [3, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row063_valid : Valid row063 := by decide
theorem row063_exact : ExactFormula row063.basis row063.formulaCost ∧
    ExactDepth row063.basis row063.depthCost :=
  valid_generating row063 row063_valid rfl

-- 64: X, NOT_Y; evidence basis_ids=[3, 10]
def row064 : Row where
  basis := [3, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row064_valid : Valid row064 := by decide
theorem row064_blocked : Blocked row064.basis :=
  valid_blocked row064 row064_valid rfl

-- 65: X, Y_IMPLIES_X; evidence basis_ids=[3, 11]
def row065 : Row where
  basis := [3, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row065_valid : Valid row065 := by decide
theorem row065_exact : ExactFormula row065.basis row065.formulaCost ∧
    ExactDepth row065.basis row065.depthCost :=
  valid_generating row065 row065_valid rfl

-- 66: X, NOT_X; evidence basis_ids=[3, 12]
def row066 : Row where
  basis := [3, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row066_valid : Valid row066 := by decide
theorem row066_blocked : Blocked row066.basis :=
  valid_blocked row066 row066_valid rfl

-- 67: X, X_IMPLIES_Y; evidence basis_ids=[3, 13]
def row067 : Row where
  basis := [3, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row067_valid : Valid row067 := by decide
theorem row067_exact : ExactFormula row067.basis row067.formulaCost ∧
    ExactDepth row067.basis row067.depthCost :=
  valid_generating row067 row067_valid rfl

-- 68: X, NAND; evidence basis_ids=[3, 14]
def row068 : Row where
  basis := [3, 14]
  formulaWeight := fun | .zero => 5 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
theorem row068_valid : Valid row068 := by decide
theorem row068_exact : ExactFormula row068.basis row068.formulaCost ∧
    ExactDepth row068.basis row068.depthCost :=
  valid_generating row068 row068_valid rfl

-- 69: X, TRUE; evidence basis_ids=[3, 15]
def row069 : Row where
  basis := [3, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row069_valid : Valid row069 := by decide
theorem row069_exact : ExactFormula row069.basis row069.formulaCost ∧
    ExactDepth row069.basis row069.depthCost :=
  valid_generating row069 row069_valid rfl

-- 70: NOT_X_AND_Y, Y; evidence basis_ids=[4, 5]
def row070 : Row where
  basis := [4, 5]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row070_valid : Valid row070 := by decide
theorem row070_blocked : Blocked row070.basis :=
  valid_blocked row070 row070_valid rfl

-- 71: NOT_X_AND_Y, XOR; evidence basis_ids=[4, 6]
def row071 : Row where
  basis := [4, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row071_valid : Valid row071 := by decide
theorem row071_blocked : Blocked row071.basis :=
  valid_blocked row071 row071_valid rfl

-- 72: NOT_X_AND_Y, OR; evidence basis_ids=[4, 7]
def row072 : Row where
  basis := [4, 7]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row072_valid : Valid row072 := by decide
theorem row072_blocked : Blocked row072.basis :=
  valid_blocked row072 row072_valid rfl

-- 73: NOT_X_AND_Y, NOR; evidence basis_ids=[4, 8]
def row073 : Row where
  basis := [4, 8]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 2
  formulaWitness := (.gate 8 (.gate 4 .leaf .leaf) (.gate 4 .leaf .leaf))
  depthWitness := (.gate 8 (.gate 4 .leaf .leaf) (.gate 4 .leaf .leaf))
theorem row073_valid : Valid row073 := by decide
theorem row073_exact : ExactFormula row073.basis row073.formulaCost ∧
    ExactDepth row073.basis row073.depthCost :=
  valid_generating row073 row073_valid rfl

-- 74: NOT_X_AND_Y, XNOR; evidence basis_ids=[4, 9]
def row074 : Row where
  basis := [4, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row074_valid : Valid row074 := by decide
theorem row074_exact : ExactFormula row074.basis row074.formulaCost ∧
    ExactDepth row074.basis row074.depthCost :=
  valid_generating row074 row074_valid rfl

-- 75: NOT_X_AND_Y, NOT_Y; evidence basis_ids=[4, 10]
def row075 : Row where
  basis := [4, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 10 .leaf (.gate 4 .leaf .leaf))
  depthWitness := (.gate 10 (.gate 4 .leaf .leaf) (.gate 4 .leaf .leaf))
theorem row075_valid : Valid row075 := by decide
theorem row075_exact : ExactFormula row075.basis row075.formulaCost ∧
    ExactDepth row075.basis row075.depthCost :=
  valid_generating row075 row075_valid rfl

-- 76: NOT_X_AND_Y, Y_IMPLIES_X; evidence basis_ids=[4, 11]
def row076 : Row where
  basis := [4, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row076_valid : Valid row076 := by decide
theorem row076_exact : ExactFormula row076.basis row076.formulaCost ∧
    ExactDepth row076.basis row076.depthCost :=
  valid_generating row076 row076_valid rfl

-- 77: NOT_X_AND_Y, NOT_X; evidence basis_ids=[4, 12]
def row077 : Row where
  basis := [4, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 12 (.gate 4 .leaf .leaf) .leaf)
  depthWitness := (.gate 12 (.gate 4 .leaf .leaf) (.gate 4 .leaf .leaf))
theorem row077_valid : Valid row077 := by decide
theorem row077_exact : ExactFormula row077.basis row077.formulaCost ∧
    ExactDepth row077.basis row077.depthCost :=
  valid_generating row077 row077_valid rfl

-- 78: NOT_X_AND_Y, X_IMPLIES_Y; evidence basis_ids=[4, 13]
def row078 : Row where
  basis := [4, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row078_valid : Valid row078 := by decide
theorem row078_exact : ExactFormula row078.basis row078.formulaCost ∧
    ExactDepth row078.basis row078.depthCost :=
  valid_generating row078 row078_valid rfl

-- 79: NOT_X_AND_Y, NAND; evidence basis_ids=[4, 14]
def row079 : Row where
  basis := [4, 14]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 (.gate 4 .leaf .leaf) .leaf)
  depthWitness := (.gate 14 (.gate 4 .leaf .leaf) (.gate 4 .leaf .leaf))
theorem row079_valid : Valid row079 := by decide
theorem row079_exact : ExactFormula row079.basis row079.formulaCost ∧
    ExactDepth row079.basis row079.depthCost :=
  valid_generating row079 row079_valid rfl

-- 80: NOT_X_AND_Y, TRUE; evidence basis_ids=[4, 15]
def row080 : Row where
  basis := [4, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row080_valid : Valid row080 := by decide
theorem row080_exact : ExactFormula row080.basis row080.formulaCost ∧
    ExactDepth row080.basis row080.depthCost :=
  valid_generating row080 row080_valid rfl

-- 81: Y, XOR; evidence basis_ids=[5, 6]
def row081 : Row where
  basis := [5, 6]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row081_valid : Valid row081 := by decide
theorem row081_blocked : Blocked row081.basis :=
  valid_blocked row081 row081_valid rfl

-- 82: Y, OR; evidence basis_ids=[5, 7]
def row082 : Row where
  basis := [5, 7]
  formulaWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  depthWeight := fun | .zero => 0 | .var => 0 | .neg => 0 | .one => 0
  reachable := fun | .zero => false | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row082_valid : Valid row082 := by decide
theorem row082_blocked : Blocked row082.basis :=
  valid_blocked row082 row082_valid rfl

-- 83: Y, NOR; evidence basis_ids=[5, 8]
def row083 : Row where
  basis := [5, 8]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 5
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 5
  depthCost := 3
  formulaWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
  depthWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
theorem row083_valid : Valid row083 := by decide
theorem row083_exact : ExactFormula row083.basis row083.formulaCost ∧
    ExactDepth row083.basis row083.depthCost :=
  valid_generating row083 row083_valid rfl

-- 84: Y, XNOR; evidence basis_ids=[5, 9]
def row084 : Row where
  basis := [5, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row084_valid : Valid row084 := by decide
theorem row084_exact : ExactFormula row084.basis row084.formulaCost ∧
    ExactDepth row084.basis row084.depthCost :=
  valid_generating row084 row084_valid rfl

-- 85: Y, NOT_Y; evidence basis_ids=[5, 10]
def row085 : Row where
  basis := [5, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row085_valid : Valid row085 := by decide
theorem row085_blocked : Blocked row085.basis :=
  valid_blocked row085 row085_valid rfl

-- 86: Y, Y_IMPLIES_X; evidence basis_ids=[5, 11]
def row086 : Row where
  basis := [5, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row086_valid : Valid row086 := by decide
theorem row086_exact : ExactFormula row086.basis row086.formulaCost ∧
    ExactDepth row086.basis row086.depthCost :=
  valid_generating row086 row086_valid rfl

-- 87: Y, NOT_X; evidence basis_ids=[5, 12]
def row087 : Row where
  basis := [5, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row087_valid : Valid row087 := by decide
theorem row087_blocked : Blocked row087.basis :=
  valid_blocked row087 row087_valid rfl

-- 88: Y, X_IMPLIES_Y; evidence basis_ids=[5, 13]
def row088 : Row where
  basis := [5, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row088_valid : Valid row088 := by decide
theorem row088_exact : ExactFormula row088.basis row088.formulaCost ∧
    ExactDepth row088.basis row088.depthCost :=
  valid_generating row088 row088_valid rfl

-- 89: Y, NAND; evidence basis_ids=[5, 14]
def row089 : Row where
  basis := [5, 14]
  formulaWeight := fun | .zero => 5 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 14 .leaf .leaf))
theorem row089_valid : Valid row089 := by decide
theorem row089_exact : ExactFormula row089.basis row089.formulaCost ∧
    ExactDepth row089.basis row089.depthCost :=
  valid_generating row089 row089_valid rfl

-- 90: Y, TRUE; evidence basis_ids=[5, 15]
def row090 : Row where
  basis := [5, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row090_valid : Valid row090 := by decide
theorem row090_exact : ExactFormula row090.basis row090.formulaCost ∧
    ExactDepth row090.basis row090.depthCost :=
  valid_generating row090 row090_valid rfl

-- 91: XOR, OR; evidence basis_ids=[6, 7]
def row091 : Row where
  basis := [6, 7]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => false | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row091_valid : Valid row091 := by decide
theorem row091_blocked : Blocked row091.basis :=
  valid_blocked row091 row091_valid rfl

-- 92: XOR, NOR; evidence basis_ids=[6, 8]
def row092 : Row where
  basis := [6, 8]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 6 .leaf (.gate 8 .leaf .leaf))
  depthWitness := (.gate 6 .leaf (.gate 8 .leaf .leaf))
theorem row092_valid : Valid row092 := by decide
theorem row092_exact : ExactFormula row092.basis row092.formulaCost ∧
    ExactDepth row092.basis row092.depthCost :=
  valid_generating row092 row092_valid rfl

-- 93: XOR, XNOR; evidence basis_ids=[6, 9]
def row093 : Row where
  basis := [6, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row093_valid : Valid row093 := by decide
theorem row093_exact : ExactFormula row093.basis row093.formulaCost ∧
    ExactDepth row093.basis row093.depthCost :=
  valid_generating row093 row093_valid rfl

-- 94: XOR, NOT_Y; evidence basis_ids=[6, 10]
def row094 : Row where
  basis := [6, 10]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 6 .leaf (.gate 10 .leaf .leaf))
  depthWitness := (.gate 6 .leaf (.gate 10 .leaf .leaf))
theorem row094_valid : Valid row094 := by decide
theorem row094_exact : ExactFormula row094.basis row094.formulaCost ∧
    ExactDepth row094.basis row094.depthCost :=
  valid_generating row094 row094_valid rfl

-- 95: XOR, Y_IMPLIES_X; evidence basis_ids=[6, 11]
def row095 : Row where
  basis := [6, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row095_valid : Valid row095 := by decide
theorem row095_exact : ExactFormula row095.basis row095.formulaCost ∧
    ExactDepth row095.basis row095.depthCost :=
  valid_generating row095 row095_valid rfl

-- 96: XOR, NOT_X; evidence basis_ids=[6, 12]
def row096 : Row where
  basis := [6, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 6 .leaf (.gate 12 .leaf .leaf))
  depthWitness := (.gate 6 .leaf (.gate 12 .leaf .leaf))
theorem row096_valid : Valid row096 := by decide
theorem row096_exact : ExactFormula row096.basis row096.formulaCost ∧
    ExactDepth row096.basis row096.depthCost :=
  valid_generating row096 row096_valid rfl

-- 97: XOR, X_IMPLIES_Y; evidence basis_ids=[6, 13]
def row097 : Row where
  basis := [6, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row097_valid : Valid row097 := by decide
theorem row097_exact : ExactFormula row097.basis row097.formulaCost ∧
    ExactDepth row097.basis row097.depthCost :=
  valid_generating row097 row097_valid rfl

-- 98: XOR, NAND; evidence basis_ids=[6, 14]
def row098 : Row where
  basis := [6, 14]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 6 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 6 .leaf (.gate 14 .leaf .leaf))
theorem row098_valid : Valid row098 := by decide
theorem row098_exact : ExactFormula row098.basis row098.formulaCost ∧
    ExactDepth row098.basis row098.depthCost :=
  valid_generating row098 row098_valid rfl

-- 99: XOR, TRUE; evidence basis_ids=[6, 15]
def row099 : Row where
  basis := [6, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 2 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row099_valid : Valid row099 := by decide
theorem row099_exact : ExactFormula row099.basis row099.formulaCost ∧
    ExactDepth row099.basis row099.depthCost :=
  valid_generating row099 row099_valid rfl

-- 100: OR, NOR; evidence basis_ids=[7, 8]
def row100 : Row where
  basis := [7, 8]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 7 .leaf (.gate 8 .leaf .leaf))
  depthWitness := (.gate 7 .leaf (.gate 8 .leaf .leaf))
theorem row100_valid : Valid row100 := by decide
theorem row100_exact : ExactFormula row100.basis row100.formulaCost ∧
    ExactDepth row100.basis row100.depthCost :=
  valid_generating row100 row100_valid rfl

-- 101: OR, XNOR; evidence basis_ids=[7, 9]
def row101 : Row where
  basis := [7, 9]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row101_valid : Valid row101 := by decide
theorem row101_exact : ExactFormula row101.basis row101.formulaCost ∧
    ExactDepth row101.basis row101.depthCost :=
  valid_generating row101 row101_valid rfl

-- 102: OR, NOT_Y; evidence basis_ids=[7, 10]
def row102 : Row where
  basis := [7, 10]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 7 .leaf (.gate 10 .leaf .leaf))
  depthWitness := (.gate 7 .leaf (.gate 10 .leaf .leaf))
theorem row102_valid : Valid row102 := by decide
theorem row102_exact : ExactFormula row102.basis row102.formulaCost ∧
    ExactDepth row102.basis row102.depthCost :=
  valid_generating row102 row102_valid rfl

-- 103: OR, Y_IMPLIES_X; evidence basis_ids=[7, 11]
def row103 : Row where
  basis := [7, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row103_valid : Valid row103 := by decide
theorem row103_exact : ExactFormula row103.basis row103.formulaCost ∧
    ExactDepth row103.basis row103.depthCost :=
  valid_generating row103 row103_valid rfl

-- 104: OR, NOT_X; evidence basis_ids=[7, 12]
def row104 : Row where
  basis := [7, 12]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 7 .leaf (.gate 12 .leaf .leaf))
  depthWitness := (.gate 7 .leaf (.gate 12 .leaf .leaf))
theorem row104_valid : Valid row104 := by decide
theorem row104_exact : ExactFormula row104.basis row104.formulaCost ∧
    ExactDepth row104.basis row104.depthCost :=
  valid_generating row104 row104_valid rfl

-- 105: OR, X_IMPLIES_Y; evidence basis_ids=[7, 13]
def row105 : Row where
  basis := [7, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row105_valid : Valid row105 := by decide
theorem row105_exact : ExactFormula row105.basis row105.formulaCost ∧
    ExactDepth row105.basis row105.depthCost :=
  valid_generating row105 row105_valid rfl

-- 106: OR, NAND; evidence basis_ids=[7, 14]
def row106 : Row where
  basis := [7, 14]
  formulaWeight := fun | .zero => 5 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 7 .leaf (.gate 14 .leaf .leaf))
  depthWitness := (.gate 7 .leaf (.gate 14 .leaf .leaf))
theorem row106_valid : Valid row106 := by decide
theorem row106_exact : ExactFormula row106.basis row106.formulaCost ∧
    ExactDepth row106.basis row106.depthCost :=
  valid_generating row106 row106_valid rfl

-- 107: OR, TRUE; evidence basis_ids=[7, 15]
def row107 : Row where
  basis := [7, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row107_valid : Valid row107 := by decide
theorem row107_exact : ExactFormula row107.basis row107.formulaCost ∧
    ExactDepth row107.basis row107.depthCost :=
  valid_generating row107 row107_valid rfl

-- 108: NOR, XNOR; evidence basis_ids=[8, 9]
def row108 : Row where
  basis := [8, 9]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row108_valid : Valid row108 := by decide
theorem row108_exact : ExactFormula row108.basis row108.formulaCost ∧
    ExactDepth row108.basis row108.depthCost :=
  valid_generating row108 row108_valid rfl

-- 109: NOR, NOT_Y; evidence basis_ids=[8, 10]
def row109 : Row where
  basis := [8, 10]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 3
  formulaWitness := (.gate 10 .leaf (.gate 8 .leaf (.gate 8 .leaf .leaf)))
  depthWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
theorem row109_valid : Valid row109 := by decide
theorem row109_exact : ExactFormula row109.basis row109.formulaCost ∧
    ExactDepth row109.basis row109.depthCost :=
  valid_generating row109 row109_valid rfl

-- 110: NOR, Y_IMPLIES_X; evidence basis_ids=[8, 11]
def row110 : Row where
  basis := [8, 11]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row110_valid : Valid row110 := by decide
theorem row110_exact : ExactFormula row110.basis row110.formulaCost ∧
    ExactDepth row110.basis row110.depthCost :=
  valid_generating row110 row110_valid rfl

-- 111: NOR, NOT_X; evidence basis_ids=[8, 12]
def row111 : Row where
  basis := [8, 12]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 3
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 3
  depthCost := 3
  formulaWitness := (.gate 12 (.gate 8 .leaf (.gate 8 .leaf .leaf)) .leaf)
  depthWitness := (.gate 8 (.gate 8 .leaf (.gate 8 .leaf .leaf)) (.gate 8 .leaf (.gate 8 .leaf .leaf)))
theorem row111_valid : Valid row111 := by decide
theorem row111_exact : ExactFormula row111.basis row111.formulaCost ∧
    ExactDepth row111.basis row111.depthCost :=
  valid_generating row111 row111_valid rfl

-- 112: NOR, X_IMPLIES_Y; evidence basis_ids=[8, 13]
def row112 : Row where
  basis := [8, 13]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row112_valid : Valid row112 := by decide
theorem row112_exact : ExactFormula row112.basis row112.formulaCost ∧
    ExactDepth row112.basis row112.depthCost :=
  valid_generating row112 row112_valid rfl

-- 113: NOR, NAND; evidence basis_ids=[8, 14]
def row113 : Row where
  basis := [8, 14]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 8 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 8 .leaf .leaf))
theorem row113_valid : Valid row113 := by decide
theorem row113_exact : ExactFormula row113.basis row113.formulaCost ∧
    ExactDepth row113.basis row113.depthCost :=
  valid_generating row113 row113_valid rfl

-- 114: NOR, TRUE; evidence basis_ids=[8, 15]
def row114 : Row where
  basis := [8, 15]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row114_valid : Valid row114 := by decide
theorem row114_exact : ExactFormula row114.basis row114.formulaCost ∧
    ExactDepth row114.basis row114.depthCost :=
  valid_generating row114 row114_valid rfl

-- 115: XNOR, NOT_Y; evidence basis_ids=[9, 10]
def row115 : Row where
  basis := [9, 10]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row115_valid : Valid row115 := by decide
theorem row115_exact : ExactFormula row115.basis row115.formulaCost ∧
    ExactDepth row115.basis row115.depthCost :=
  valid_generating row115 row115_valid rfl

-- 116: XNOR, Y_IMPLIES_X; evidence basis_ids=[9, 11]
def row116 : Row where
  basis := [9, 11]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row116_valid : Valid row116 := by decide
theorem row116_exact : ExactFormula row116.basis row116.formulaCost ∧
    ExactDepth row116.basis row116.depthCost :=
  valid_generating row116 row116_valid rfl

-- 117: XNOR, NOT_X; evidence basis_ids=[9, 12]
def row117 : Row where
  basis := [9, 12]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row117_valid : Valid row117 := by decide
theorem row117_exact : ExactFormula row117.basis row117.formulaCost ∧
    ExactDepth row117.basis row117.depthCost :=
  valid_generating row117 row117_valid rfl

-- 118: XNOR, X_IMPLIES_Y; evidence basis_ids=[9, 13]
def row118 : Row where
  basis := [9, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row118_valid : Valid row118 := by decide
theorem row118_exact : ExactFormula row118.basis row118.formulaCost ∧
    ExactDepth row118.basis row118.depthCost :=
  valid_generating row118 row118_valid rfl

-- 119: XNOR, NAND; evidence basis_ids=[9, 14]
def row119 : Row where
  basis := [9, 14]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row119_valid : Valid row119 := by decide
theorem row119_exact : ExactFormula row119.basis row119.formulaCost ∧
    ExactDepth row119.basis row119.depthCost :=
  valid_generating row119 row119_valid rfl

-- 120: XNOR, TRUE; evidence basis_ids=[9, 15]
def row120 : Row where
  basis := [9, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 9 .leaf .leaf)
  depthWitness := (.gate 9 .leaf .leaf)
theorem row120_valid : Valid row120 := by decide
theorem row120_exact : ExactFormula row120.basis row120.formulaCost ∧
    ExactDepth row120.basis row120.depthCost :=
  valid_generating row120 row120_valid rfl

-- 121: NOT_Y, Y_IMPLIES_X; evidence basis_ids=[10, 11]
def row121 : Row where
  basis := [10, 11]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row121_valid : Valid row121 := by decide
theorem row121_exact : ExactFormula row121.basis row121.formulaCost ∧
    ExactDepth row121.basis row121.depthCost :=
  valid_generating row121 row121_valid rfl

-- 122: NOT_Y, NOT_X; evidence basis_ids=[10, 12]
def row122 : Row where
  basis := [10, 12]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => true | .one => false
  generates := false
  formulaCost := 0
  depthCost := 0
  formulaWitness := .leaf
  depthWitness := .leaf
theorem row122_valid : Valid row122 := by decide
theorem row122_blocked : Blocked row122.basis :=
  valid_blocked row122 row122_valid rfl

-- 123: NOT_Y, X_IMPLIES_Y; evidence basis_ids=[10, 13]
def row123 : Row where
  basis := [10, 13]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row123_valid : Valid row123 := by decide
theorem row123_exact : ExactFormula row123.basis row123.formulaCost ∧
    ExactDepth row123.basis row123.depthCost :=
  valid_generating row123 row123_valid rfl

-- 124: NOT_Y, NAND; evidence basis_ids=[10, 14]
def row124 : Row where
  basis := [10, 14]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 10 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 10 .leaf .leaf))
theorem row124_valid : Valid row124 := by decide
theorem row124_exact : ExactFormula row124.basis row124.formulaCost ∧
    ExactDepth row124.basis row124.depthCost :=
  valid_generating row124 row124_valid rfl

-- 125: NOT_Y, TRUE; evidence basis_ids=[10, 15]
def row125 : Row where
  basis := [10, 15]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row125_valid : Valid row125 := by decide
theorem row125_exact : ExactFormula row125.basis row125.formulaCost ∧
    ExactDepth row125.basis row125.depthCost :=
  valid_generating row125 row125_valid rfl

-- 126: Y_IMPLIES_X, NOT_X; evidence basis_ids=[11, 12]
def row126 : Row where
  basis := [11, 12]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row126_valid : Valid row126 := by decide
theorem row126_exact : ExactFormula row126.basis row126.formulaCost ∧
    ExactDepth row126.basis row126.depthCost :=
  valid_generating row126 row126_valid rfl

-- 127: Y_IMPLIES_X, X_IMPLIES_Y; evidence basis_ids=[11, 13]
def row127 : Row where
  basis := [11, 13]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row127_valid : Valid row127 := by decide
theorem row127_exact : ExactFormula row127.basis row127.formulaCost ∧
    ExactDepth row127.basis row127.depthCost :=
  valid_generating row127 row127_valid rfl

-- 128: Y_IMPLIES_X, NAND; evidence basis_ids=[11, 14]
def row128 : Row where
  basis := [11, 14]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row128_valid : Valid row128 := by decide
theorem row128_exact : ExactFormula row128.basis row128.formulaCost ∧
    ExactDepth row128.basis row128.depthCost :=
  valid_generating row128 row128_valid rfl

-- 129: Y_IMPLIES_X, TRUE; evidence basis_ids=[11, 15]
def row129 : Row where
  basis := [11, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 11 .leaf .leaf)
  depthWitness := (.gate 11 .leaf .leaf)
theorem row129_valid : Valid row129 := by decide
theorem row129_exact : ExactFormula row129.basis row129.formulaCost ∧
    ExactDepth row129.basis row129.depthCost :=
  valid_generating row129 row129_valid rfl

-- 130: NOT_X, X_IMPLIES_Y; evidence basis_ids=[12, 13]
def row130 : Row where
  basis := [12, 13]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row130_valid : Valid row130 := by decide
theorem row130_exact : ExactFormula row130.basis row130.formulaCost ∧
    ExactDepth row130.basis row130.depthCost :=
  valid_generating row130 row130_valid rfl

-- 131: NOT_X, NAND; evidence basis_ids=[12, 14]
def row131 : Row where
  basis := [12, 14]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  depthWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 2
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 2
  depthCost := 2
  formulaWitness := (.gate 14 .leaf (.gate 12 .leaf .leaf))
  depthWitness := (.gate 14 .leaf (.gate 12 .leaf .leaf))
theorem row131_valid : Valid row131 := by decide
theorem row131_exact : ExactFormula row131.basis row131.formulaCost ∧
    ExactDepth row131.basis row131.depthCost :=
  valid_generating row131 row131_valid rfl

-- 132: NOT_X, TRUE; evidence basis_ids=[12, 15]
def row132 : Row where
  basis := [12, 15]
  formulaWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row132_valid : Valid row132 := by decide
theorem row132_exact : ExactFormula row132.basis row132.formulaCost ∧
    ExactDepth row132.basis row132.depthCost :=
  valid_generating row132 row132_valid rfl

-- 133: X_IMPLIES_Y, NAND; evidence basis_ids=[13, 14]
def row133 : Row where
  basis := [13, 14]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row133_valid : Valid row133 := by decide
theorem row133_exact : ExactFormula row133.basis row133.formulaCost ∧
    ExactDepth row133.basis row133.depthCost :=
  valid_generating row133 row133_valid rfl

-- 134: X_IMPLIES_Y, TRUE; evidence basis_ids=[13, 15]
def row134 : Row where
  basis := [13, 15]
  formulaWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 1 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => false | .var => true | .neg => false | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 13 .leaf .leaf)
  depthWitness := (.gate 13 .leaf .leaf)
theorem row134_valid : Valid row134 := by decide
theorem row134_exact : ExactFormula row134.basis row134.formulaCost ∧
    ExactDepth row134.basis row134.depthCost :=
  valid_generating row134 row134_valid rfl

-- 135: NAND, TRUE; evidence basis_ids=[14, 15]
def row135 : Row where
  basis := [14, 15]
  formulaWeight := fun | .zero => 3 | .var => 0 | .neg => 1 | .one => 1
  depthWeight := fun | .zero => 2 | .var => 0 | .neg => 1 | .one => 1
  reachable := fun | .zero => true | .var => true | .neg => true | .one => true
  generates := true
  formulaCost := 1
  depthCost := 1
  formulaWitness := (.gate 15 .leaf .leaf)
  depthWitness := (.gate 15 .leaf .leaf)
theorem row135_valid : Valid row135 := by decide
theorem row135_exact : ExactFormula row135.basis row135.formulaCost ∧
    ExactDepth row135.basis row135.depthCost :=
  valid_generating row135 row135_valid rfl

def rows : List Row := [
  row000,
  row001,
  row002,
  row003,
  row004,
  row005,
  row006,
  row007,
  row008,
  row009,
  row010,
  row011,
  row012,
  row013,
  row014,
  row015,
  row016,
  row017,
  row018,
  row019,
  row020,
  row021,
  row022,
  row023,
  row024,
  row025,
  row026,
  row027,
  row028,
  row029,
  row030,
  row031,
  row032,
  row033,
  row034,
  row035,
  row036,
  row037,
  row038,
  row039,
  row040,
  row041,
  row042,
  row043,
  row044,
  row045,
  row046,
  row047,
  row048,
  row049,
  row050,
  row051,
  row052,
  row053,
  row054,
  row055,
  row056,
  row057,
  row058,
  row059,
  row060,
  row061,
  row062,
  row063,
  row064,
  row065,
  row066,
  row067,
  row068,
  row069,
  row070,
  row071,
  row072,
  row073,
  row074,
  row075,
  row076,
  row077,
  row078,
  row079,
  row080,
  row081,
  row082,
  row083,
  row084,
  row085,
  row086,
  row087,
  row088,
  row089,
  row090,
  row091,
  row092,
  row093,
  row094,
  row095,
  row096,
  row097,
  row098,
  row099,
  row100,
  row101,
  row102,
  row103,
  row104,
  row105,
  row106,
  row107,
  row108,
  row109,
  row110,
  row111,
  row112,
  row113,
  row114,
  row115,
  row116,
  row117,
  row118,
  row119,
  row120,
  row121,
  row122,
  row123,
  row124,
  row125,
  row126,
  row127,
  row128,
  row129,
  row130,
  row131,
  row132,
  row133,
  row134,
  row135
]

theorem rows_count : rows.length = 136 := by decide
theorem generating_count : (rows.filter fun r => r.generates).length = 93 := by decide
theorem blocked_count : (rows.filter fun r => !r.generates).length = 43 := by decide

/-- The recorded population consists of every singleton and distinct unordered pair. -/
def expectedBases : List (List Op) :=
  (List.finRange 16).map (fun a => [a]) ++
  (List.finRange 16).flatMap (fun a =>
    ((List.finRange 16).filter (fun b => a.val < b.val)).map (fun b => [a,b]))

theorem population_complete : rows.map Row.basis = expectedBases := by decide

def AllValid : List Row → Prop
  | [] => True
  | r :: rest => Valid r ∧ AllValid rest

theorem all_rows_valid : AllValid rows := by
  exact ⟨row000_valid, ⟨row001_valid, ⟨row002_valid, ⟨row003_valid, ⟨row004_valid, ⟨row005_valid, ⟨row006_valid, ⟨row007_valid, ⟨row008_valid, ⟨row009_valid, ⟨row010_valid, ⟨row011_valid, ⟨row012_valid, ⟨row013_valid, ⟨row014_valid, ⟨row015_valid, ⟨row016_valid, ⟨row017_valid, ⟨row018_valid, ⟨row019_valid, ⟨row020_valid, ⟨row021_valid, ⟨row022_valid, ⟨row023_valid, ⟨row024_valid, ⟨row025_valid, ⟨row026_valid, ⟨row027_valid, ⟨row028_valid, ⟨row029_valid, ⟨row030_valid, ⟨row031_valid, ⟨row032_valid, ⟨row033_valid, ⟨row034_valid, ⟨row035_valid, ⟨row036_valid, ⟨row037_valid, ⟨row038_valid, ⟨row039_valid, ⟨row040_valid, ⟨row041_valid, ⟨row042_valid, ⟨row043_valid, ⟨row044_valid, ⟨row045_valid, ⟨row046_valid, ⟨row047_valid, ⟨row048_valid, ⟨row049_valid, ⟨row050_valid, ⟨row051_valid, ⟨row052_valid, ⟨row053_valid, ⟨row054_valid, ⟨row055_valid, ⟨row056_valid, ⟨row057_valid, ⟨row058_valid, ⟨row059_valid, ⟨row060_valid, ⟨row061_valid, ⟨row062_valid, ⟨row063_valid, ⟨row064_valid, ⟨row065_valid, ⟨row066_valid, ⟨row067_valid, ⟨row068_valid, ⟨row069_valid, ⟨row070_valid, ⟨row071_valid, ⟨row072_valid, ⟨row073_valid, ⟨row074_valid, ⟨row075_valid, ⟨row076_valid, ⟨row077_valid, ⟨row078_valid, ⟨row079_valid, ⟨row080_valid, ⟨row081_valid, ⟨row082_valid, ⟨row083_valid, ⟨row084_valid, ⟨row085_valid, ⟨row086_valid, ⟨row087_valid, ⟨row088_valid, ⟨row089_valid, ⟨row090_valid, ⟨row091_valid, ⟨row092_valid, ⟨row093_valid, ⟨row094_valid, ⟨row095_valid, ⟨row096_valid, ⟨row097_valid, ⟨row098_valid, ⟨row099_valid, ⟨row100_valid, ⟨row101_valid, ⟨row102_valid, ⟨row103_valid, ⟨row104_valid, ⟨row105_valid, ⟨row106_valid, ⟨row107_valid, ⟨row108_valid, ⟨row109_valid, ⟨row110_valid, ⟨row111_valid, ⟨row112_valid, ⟨row113_valid, ⟨row114_valid, ⟨row115_valid, ⟨row116_valid, ⟨row117_valid, ⟨row118_valid, ⟨row119_valid, ⟨row120_valid, ⟨row121_valid, ⟨row122_valid, ⟨row123_valid, ⟨row124_valid, ⟨row125_valid, ⟨row126_valid, ⟨row127_valid, ⟨row128_valid, ⟨row129_valid, ⟨row130_valid, ⟨row131_valid, ⟨row132_valid, ⟨row133_valid, ⟨row134_valid, ⟨row135_valid, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem allValid_member {rs : List Row} (h : AllValid rs) {r : Row}
    (hm : r ∈ rs) : Valid r := by
  induction rs with
  | nil => simp at hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with heq | hrest
    · subst r; exact h.1
    · exact ih h.2 hrest

/-- Every listed generating basis has the stated exact formula and depth costs. -/
theorem every_generating_row {r : Row} (hm : r ∈ rows) (hg : r.generates = true) :
    ExactFormula r.basis r.formulaCost ∧ ExactDepth r.basis r.depthCost :=
  valid_generating r (allValid_member all_rows_valid hm) hg

/-- Every listed non-generating basis is blocked at every finite size/depth. -/
theorem every_blocked_row {r : Row} (hm : r ∈ rows) (hg : r.generates = false) :
    Blocked r.basis := valid_blocked r (allValid_member all_rows_valid hm) hg

/-- All 136 results lift to every nonempty variable collection, with unchanged costs. -/
theorem every_generating_row_over {α : Type} (x : α) {r : Row}
    (hm : r ∈ rows) (hg : r.generates = true) :
    ExactFormulaOver α r.basis r.formulaCost ∧ ExactDepthOver α r.basis r.depthCost := by
  have h := every_generating_row hm hg
  exact ⟨exactFormula_over x h.1, exactDepth_over x h.2⟩

theorem every_blocked_row_over {α : Type} {r : Row}
    (hm : r ∈ rows) (hg : r.generates = false)
    (t : Formula α) (ha : t.allowed r.basis) : ¬t.tautology :=
  blocked_over (every_blocked_row hm hg) t ha

end
end FIG22.Basis
