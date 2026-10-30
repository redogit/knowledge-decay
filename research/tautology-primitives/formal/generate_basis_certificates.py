#!/usr/bin/env python3
"""Reproduce finite Lean certificates from the recorded FIG-22 population.

Python proposes witnesses and potentials; Lean's kernel checks every finite
inequality and the structural-induction soundness theorem. This script is not
part of the trusted proof boundary.
"""
from __future__ import annotations
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from circuit_costs import all_unary_minima

HEADER = r'''import Std

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

'''


DAG_HEADER = r'''import BasisCertificates

/-!
# Reachable-node DAG costs for all 136 FIG-22 bases

A gate has an immutable index, an arbitrary operation from the full ordered
sixteen-function domain, and ordered references to strictly earlier gates or
variable sources. The output may select any node, and dead allocated gates
are excluded from cost. The lower-bound bridge unfolds the DAG without
changing depth and proves depth ≤ the number of distinct output ancestors.
-/
namespace FIG22.Basis

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

inductive Ref (α : Type) (k : Nat) where
  | input : α → Ref α k
  | gate : Fin k → Ref α k
  deriving Repr

structure Dag (α : Type) where
  allocated : Nat
  label : Fin allocated → Op
  pins : (i : Fin allocated) → Ref α i.val × Ref α i.val
  output : Ref α allocated

/-- Unfolding copies occurrences but keeps every ordered gate application. -/
def Dag.unfold (c : Dag α) {k : Nat} (hk : k ≤ c.allocated) :
    Ref α k → Formula α
  | .input x => .leaf x
  | .gate i =>
    let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
    .gate (c.label j) (c.unfold h (c.pins j).1) (c.unfold h (c.pins j).2)
termination_by k

/-- Distinct gate indices in the ancestry of the selected reference. -/
def Dag.ancestors (c : Dag α) {k : Nat} (hk : k ≤ c.allocated) :
    Ref α k → List Nat
  | .input _ => []
  | .gate i =>
    let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
    (i.val :: c.ancestors h (c.pins j).1 ++ c.ancestors h (c.pins j).2).eraseDups
termination_by k

def Dag.reachableCount (c : Dag α) : Nat :=
  (c.ancestors (Nat.le_refl _) c.output).length

def Dag.formula (c : Dag α) : Formula α :=
  c.unfold (Nat.le_refl _) c.output

def Dag.depth (c : Dag α) : Nat := c.formula.depth

def Dag.eval (c : Dag α) (v : α → Bool) : Bool := c.formula.eval v

def Dag.IsTrue (c : Dag α) : Prop := ∀ v, c.eval v = true

def Dag.Allowed (c : Dag α) (B : List Op) : Prop :=
  ∀ i : Fin c.allocated, c.label i ∈ B

 theorem dag_eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_eraseDups]
    · exact dag_eraseDups_nodup _
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun b : Nat => !b == a) xs
  simp only [List.length_cons]
  omega

 theorem Dag.ancestors_nodup (c : Dag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) : (c.ancestors hk r).Nodup := by
  cases r with
  | input x => simp [Dag.ancestors]
  | gate i => simpa only [Dag.ancestors] using dag_eraseDups_nodup _

 theorem Dag.ancestors_bounded (c : Dag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    ∀ j ∈ c.ancestors hk r, j < k := by
  cases r with
  | input x => simp [Dag.ancestors]
  | gate i =>
    intro a ha
    simp only [Dag.ancestors, List.mem_eraseDups, List.mem_cons, List.mem_append] at ha
    rcases ha with (heq | hl) | hr
    · omega
    · have hb := c.ancestors_bounded _ _ a hl
      exact Nat.lt_trans hb i.isLt
    · have hb := c.ancestors_bounded _ _ a hr
      exact Nat.lt_trans hb i.isLt
termination_by k

 theorem Dag.unfold_allowed (c : Dag α) {B : List Op} (hc : c.Allowed B)
    {k : Nat} (hk : k ≤ c.allocated) (r : Ref α k) :
    (c.unfold hk r).allowed B := by
  cases r with
  | input x => simp [Dag.unfold, Formula.allowed]
  | gate i =>
    simp only [Dag.unfold, Formula.allowed]
    exact ⟨hc _, c.unfold_allowed hc _ _, c.unfold_allowed hc _ _⟩
termination_by k

 theorem Dag.unfold_depth_le_ancestors (c : Dag α) {k : Nat}
    (hk : k ≤ c.allocated) (r : Ref α k) :
    (c.unfold hk r).depth ≤ (c.ancestors hk r).length := by
  cases r with
  | input x => simp [Dag.unfold, Formula.depth, Dag.ancestors]
  | gate i =>
    let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let hi : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
    let left := c.ancestors hi (c.pins j).1
    let right := c.ancestors hi (c.pins j).2
    let parent := (i.val :: left ++ right).eraseDups
    have hlbound := c.ancestors_bounded hi (c.pins j).1
    have hrbound := c.ancestors_bounded hi (c.pins j).2
    have hln : (i.val :: left).Nodup := by
      rw [List.nodup_cons]
      exact ⟨by intro hm; have hb := hlbound _ hm; omega,
        c.ancestors_nodup hi (c.pins j).1⟩
    have hrn : (i.val :: right).Nodup := by
      rw [List.nodup_cons]
      exact ⟨by intro hm; have hb := hrbound _ hm; omega,
        c.ancestors_nodup hi (c.pins j).2⟩
    have hlsub : i.val :: left ⊆ parent := by
      intro a ha
      simp only [parent, List.mem_eraseDups, List.mem_cons, List.mem_append]
      rcases List.mem_cons.mp ha with heq | hmem
      · exact Or.inl (Or.inl heq)
      · exact Or.inl (Or.inr hmem)
    have hrsub : i.val :: right ⊆ parent := by
      intro a ha
      simp only [parent, List.mem_eraseDups, List.mem_cons, List.mem_append]
      rcases List.mem_cons.mp ha with heq | hmem
      · exact Or.inl (Or.inl heq)
      · exact Or.inr hmem
    have hlcount := hln.length_le_of_subset hlsub
    have hrcount := hrn.length_le_of_subset hrsub
    have hldepth := c.unfold_depth_le_ancestors hi (c.pins j).1
    have hrdepth := c.unfold_depth_le_ancestors hi (c.pins j).2
    change (c.unfold hi (c.pins j).1).depth ≤ left.length at hldepth
    change (c.unfold hi (c.pins j).2).depth ≤ right.length at hrdepth
    simp only [Dag.unfold, Formula.depth, Dag.ancestors]
    change 1 + max (c.unfold hi (c.pins j).1).depth
      (c.unfold hi (c.pins j).2).depth ≤ parent.length
    simp only [List.length_cons] at hlcount hrcount
    have hl : 1 + (c.unfold hi (c.pins j).1).depth ≤ parent.length := by
      change left.length + 1 ≤ parent.length at hlcount
      omega
    have hr : 1 + (c.unfold hi (c.pins j).2).depth ≤ parent.length := by
      change right.length + 1 ≤ parent.length at hrcount
      omega
    omega
termination_by k

 theorem Dag.depth_le_reachable (c : Dag α) : c.depth ≤ c.reachableCount :=
  c.unfold_depth_le_ancestors (Nat.le_refl _) c.output

/-- Every formula depth lower bound applies to every finite DAG, including dead allocations. -/
 theorem Dag.lower_of_depth (x : α) {B : List Op} {d : Nat}
    (h : ExactDepth B d) (c : Dag α) (ha : c.Allowed B) (ht : c.IsTrue) :
    d ≤ c.reachableCount := by
  have hl := (exactDepth_over x h).2 c.formula (c.unfold_allowed ha _ _) ht
  exact Nat.le_trans hl c.depth_le_reachable

 theorem Dag.blocked_of_formula {B : List Op} (h : Blocked B) (c : Dag α)
    (ha : c.Allowed B) : ¬c.IsTrue :=
  blocked_over h c.formula (c.unfold_allowed ha _ _)

 def ExactDagOver (α : Type) (B : List Op) (n : Nat) : Prop :=
  (∃ c : Dag α, c.Allowed B ∧ c.IsTrue ∧ c.reachableCount = n) ∧
  ∀ c : Dag α, c.Allowed B → c.IsTrue → n ≤ c.reachableCount

'''


def term_from_plan(plan: dict) -> str:
    terms = ['.leaf']
    for g in plan['gates']:
        op = int(''.join(map(str, g['operator']['truth'])), 2)
        terms.append(f'(.gate {op} {terms[g["left"]]} {terms[g["right"]]})')
    return terms[plan['output']]


def function(vals: list, boolean: bool = False) -> str:
    def fmt(v):
        return str(v).lower() if boolean else str(v)
    return 'fun | .zero => ' + fmt(vals[0]) + ' | .var => ' + fmt(vals[1]) + ' | .neg => ' + fmt(vals[2]) + ' | .one => ' + fmt(vals[3])


def main() -> None:
    evidence = json.loads((ROOT / 'evidence/minimum_costs.json').read_text())
    assert len(evidence['rows']) == 136
    chunks = [HEADER]
    indices = []
    for i, row in enumerate(evidence['rows']):
        name = f'row{i:03d}'
        indices.append(name)
        minima = all_unary_minima(row['operator_names'])
        states = [(0,0), (0,1), (1,0), (1,1)]
        formula = [minima[s].formula.cost if minima[s].formula else None for s in states]
        depth = [minima[s].depth.cost if minima[s].depth else None for s in states]
        reach = [v is not None for v in formula]
        assert formula[-1] == row['minimum']['formula_gates']
        assert depth[-1] == row['minimum']['depth']
        fw = [max(v for v in formula if v is not None) if v is None else v for v in formula]
        dw = [max(v for v in depth if v is not None) if v is None else v for v in depth]
        ft = term_from_plan(row['witnesses']['formula_gates']['plan']) if reach[-1] else '.leaf'
        dt = term_from_plan(row['witnesses']['depth']['plan']) if reach[-1] else '.leaf'
        chunks.append(f'-- {i}: {", ".join(row["operator_names"])}; evidence basis_ids={row["basis_ids"]}\n')
        chunks.append(f'def {name} : Row where\n'
                      f'  basis := {row["basis_ids"]}\n'
                      f'  formulaWeight := {function(fw)}\n'
                      f'  depthWeight := {function(dw)}\n'
                      f'  reachable := {function(reach, True)}\n'
                      f'  generates := {str(reach[-1]).lower()}\n'
                      f'  formulaCost := {formula[-1] or 0}\n'
                      f'  depthCost := {depth[-1] or 0}\n'
                      f'  formulaWitness := {ft}\n'
                      f'  depthWitness := {dt}\n'
                      f'theorem {name}_valid : Valid {name} := by decide\n')
        if reach[-1]:
            chunks.append(f'theorem {name}_exact : ExactFormula {name}.basis {name}.formulaCost ∧\n'
                          f'    ExactDepth {name}.basis {name}.depthCost :=\n'
                          f'  valid_generating {name} {name}_valid rfl\n\n')
        else:
            chunks.append(f'theorem {name}_blocked : Blocked {name}.basis :=\n'
                          f'  valid_blocked {name} {name}_valid rfl\n\n')
    chunks.append('def rows : List Row := [\n  ' + ',\n  '.join(indices) + '\n]\n\n')
    chunks.append('theorem rows_count : rows.length = 136 := by decide\n')
    chunks.append('theorem generating_count : (rows.filter fun r => r.generates).length = 93 := by decide\n')
    chunks.append('theorem blocked_count : (rows.filter fun r => !r.generates).length = 43 := by decide\n')
    chunks.append('''
/-- The recorded population consists of every singleton and distinct unordered pair. -/
def expectedBases : List (List Op) :=
  (List.finRange 16).map (fun a => [a]) ++
  (List.finRange 16).flatMap (fun a =>
    ((List.finRange 16).filter (fun b => a.val < b.val)).map (fun b => [a,b]))

theorem population_complete : rows.map Row.basis = expectedBases := by decide

def AllValid : List Row → Prop
  | [] => True
  | r :: rest => Valid r ∧ AllValid rest

''')
    chunks.append('theorem all_rows_valid : AllValid rows := by\n  exact ' + ''.join(f'⟨{n}_valid, ' for n in indices) + 'True.intro' + '⟩' * len(indices) + '\n')
    chunks.append('''
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
''')
    out = ROOT / 'formal/BasisCertificates.lean'
    out.write_text(''.join(chunks))
    print(f'Wrote {out}: 136 certificates; 93 generating, 43 blocked.')
    generate_dag(evidence)


def generate_dag(evidence: dict) -> None:
    chunks = [DAG_HEADER]
    def ref(v: int) -> str:
        return '.input x' if v == 0 else f'(.gate ⟨{v-1}, by omega⟩)'
    for i, row in enumerate(evidence['rows']):
        r = f'row{i:03d}'
        name = f'dag{i:03d}'
        if row['minimum']['dag_gates'] is None:
            chunks.append(f'theorem {r}_dag_blocked (c : Dag α) (ha : c.Allowed {r}.basis) :\n'
                          f'    ¬c.IsTrue := c.blocked_of_formula {r}_blocked ha\n\n')
            continue
        plan = row['witnesses']['dag_gates']['plan']
        cost = row['minimum']['dag_gates']
        assert cost == row['minimum']['depth']
        gates = plan['gates']
        assert len(gates) == cost
        labels = [int(''.join(map(str,g['operator']['truth'])),2) for g in gates]
        label = str(labels[-1])
        for k in reversed(range(len(labels)-1)):
            label = f'if i.val = {k} then {labels[k]} else {label}'
        pins = f'({ref(gates[-1]["left"])}, {ref(gates[-1]["right"])})'
        for k in reversed(range(len(gates)-1)):
            g = gates[k]
            pins = f'if h{k} : i.val = {k} then ({ref(g["left"])}, {ref(g["right"])}) else {pins}'
        chunks.append(f'-- {i}: {", ".join(row["operator_names"])}; reachable DAG cost {cost}\n')
        chunks.append(f'def {name} (x : α) : Dag α where\n'
                      f'  allocated := {len(gates)}\n'
                      f'  label i := {label}\n'
                      f'  pins i := {pins}\n'
                      f'  output := .gate ⟨{plan["output"]-1}, by decide⟩\n\n')
        if len(gates) == 1:
            allowed_body = f'  intro i\n  simp [{name}, {r}]\n\n'
        else:
            allowed_body = (f'  intro i\n  have hi : ' + ' ∨ '.join(f'i.val = {j}' for j in range(len(gates))) + ' := by\n'
                            f'    have hb := i.isLt\n    change i.val < {len(gates)} at hb\n    omega\n'
                            '  rcases hi with ' + ' | '.join('h' for _ in gates) + '\n'
                            f'  all_goals simp [{name}, {r}, h]\n\n')
        chunks.append(f'theorem {name}_allowed (x : α) : ({name} x).Allowed {r}.basis := by\n' + allowed_body)
        chunks.append(f'theorem {name}_true (x : α) : ({name} x).IsTrue := by\n'
                      f'  intro v\n  cases hv : v x <;>\n'
                      f'    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, {name}, applyOp, hv] <;> decide\n\n')
        chunks.append(f'theorem {name}_cost (x : α) : ({name} x).reachableCount = {cost} := by\n'
                      f'  simp [Dag.reachableCount, Dag.ancestors, {name}]\n  decide\n\n')
        chunks.append(f'theorem {r}_dag_exact (x : α) : ExactDagOver α {r}.basis {cost} := by\n'
                      f'  constructor\n'
                      f'  · exact ⟨{name} x, {name}_allowed x, {name}_true x, {name}_cost x⟩\n'
                      f'  · intro c ha ht\n'
                      f'    exact c.lower_of_depth x {r}_exact.2 ha ht\n\n')
    chunks.append(r'''
/-- A single row records either exact reachable cost or an unbounded obstruction. -/
def RowDagResult (α : Type) (r : Row) : Prop :=
  if r.generates then ExactDagOver α r.basis r.depthCost
  else ∀ c : Dag α, c.Allowed r.basis → ¬c.IsTrue

def AllDagResults (α : Type) : List Row → Prop
  | [] => True
  | r :: rest => RowDagResult α r ∧ AllDagResults α rest

''')
    dag_proofs = [f'row{i:03d}_dag_exact x' if r['minimum']['dag_gates'] is not None
                  else f'row{i:03d}_dag_blocked' for i, r in enumerate(evidence['rows'])]
    chunks.append('theorem all_dag_results (x : α) : AllDagResults α rows := by\n  exact ' +
                  ''.join(f'⟨{proof}, ' for proof in dag_proofs) + 'True.intro' + '⟩' * len(dag_proofs) + '\n\n')
    chunks.append(r'''
theorem allDagResults_member {rs : List Row} (h : AllDagResults α rs) {r : Row}
    (hm : r ∈ rs) : RowDagResult α r := by
  induction rs with
  | nil => simp at hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with heq | hrest
    · subst r; exact h.1
    · exact ih h.2 hrest

/-- Uniform exact reachable-node minimum for every generating member of the population. -/
theorem every_generating_row_dag (x : α) {r : Row}
    (hm : r ∈ rows) (hg : r.generates = true) :
    ExactDagOver α r.basis r.depthCost := by
  have h := allDagResults_member (all_dag_results x) hm
  simpa only [RowDagResult, hg, ↓reduceIte] using h

/-- Uniform obstruction for every blocked member, with no allocation or depth bound. -/
theorem every_blocked_row_dag {r : Row} (hm : r ∈ rows) (hg : r.generates = false)
    (c : Dag α) (ha : c.Allowed r.basis) : ¬c.IsTrue :=
  c.blocked_of_formula (every_blocked_row hm hg) ha

/-- All three independently minimized costs; in this population shared size equals depth. -/
theorem every_generating_row_all_costs (x : α) {r : Row}
    (hm : r ∈ rows) (hg : r.generates = true) :
    ExactFormulaOver α r.basis r.formulaCost ∧
    ExactDagOver α r.basis r.depthCost ∧ ExactDepthOver α r.basis r.depthCost := by
  have hf := every_generating_row_over x hm hg
  exact ⟨hf.1, every_generating_row_dag x hm hg, hf.2⟩

/-- Exact-cost histogram for the complete singleton/pair population. -/
def costPopulation (f g d : Nat) : Nat :=
  (rows.filter fun r => r.generates && r.formulaCost == f &&
    r.depthCost == g && r.depthCost == d).length

theorem population_111 : costPopulation 1 1 1 = 58 := by decide
theorem population_222 : costPopulation 2 2 2 = 24 := by decide
theorem population_322 : costPopulation 3 2 2 = 3 := by decide
theorem population_333 : costPopulation 3 3 3 = 4 := by decide
theorem population_533 : costPopulation 5 3 3 = 4 := by decide
theorem population_no_formula_four :
    (rows.filter fun r => r.generates && r.formulaCost == 4).length = 0 := by decide
theorem population_sharing_gain :
    (rows.filter fun r => r.generates && r.depthCost < r.formulaCost).length = 7 := by decide

''')
    chunks.append('end\nend FIG22.Basis\n')
    out = ROOT / 'formal/BasisDag.lean'
    out.write_text(''.join(chunks))
    print(f'Wrote {out}: 93 exact reachable DAG minima; 43 unbounded obstructions.')

if __name__ == '__main__':
    main()
