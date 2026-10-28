import BooleanDagSupport
import TheoremTwoConsequences

/-!
# Theorem 2 for arbitrary binary Boolean functions

These results quantify over function-labelled formulas and indexed DAGs
directly. The truth-table encoding is a cost-preserving bijection, rather than
an assumption that a basis was supplied using particular numeric names.
-/

namespace FIG22.Basis.TheoremTwo

noncomputable section

def RawExactCosts (α : Type) (B : List RawOp) (f d : Nat) : Prop :=
  ExactRawFormulaOver α B f ∧ ExactRawDagOver α B d ∧ ExactRawDepthOver α B d ∧
    ExactRawDagDepthOver α B d

def RawBlockedCosts (α : Type) (B : List RawOp) : Prop :=
  (∀ t : RawFormula α, t.allowed B → ¬t.tautology) ∧
  (∀ c : RawDag α, c.Allowed B → ¬c.IsTrue)

def RawResult (α : Type) (B : List RawOp) : Branch → Prop
  | .one => RawExactCosts α B 1 1
  | .noNeg => RawBlockedCosts α B
  | .two => RawExactCosts α B 2 2
  | .threeTwo => RawExactCosts α B 3 2
  | .threeThree => RawExactCosts α B 3 3
  | .fiveThree => RawExactCosts α B 5 3
  | .final => RawBlockedCosts α B

theorem rawExactCosts_iff {α : Type} (B : List RawOp) (f d : Nat) :
    RawExactCosts α B f d ↔ ExactCosts α (encodeBasis B) f d := by
  simp only [RawExactCosts, ExactCosts, exactRawFormula_iff, exactRawDag_iff,
    exactRawDepth_iff, exactRawDagDepth_iff]

theorem rawBlockedCosts_iff {α : Type} (B : List RawOp) :
    RawBlockedCosts α B ↔ BlockedCosts α (encodeBasis B) := by
  simp only [RawBlockedCosts, BlockedCosts, rawFormula_blocked_iff, rawDag_blocked_iff]

theorem rawResult_iff {α : Type} (B : List RawOp) (b : Branch) :
    RawResult α B b ↔ Result α (encodeBasis B) b := by
  cases b <;> simp only [RawResult, Result, rawExactCosts_iff, rawBlockedCosts_iff]

/-- The full seven-row classification for arbitrary function-labelled bases. -/
theorem theorem_two_raw {α : Type} (x : α) (B : List RawOp) :
    RawResult α B (classify (encodeBasis B)) :=
  (rawResult_iff B _).2 (theorem_two x (encodeBasis B))

theorem complete_raw {α : Type} (x : α) (B : List RawOp) :
    RawBlockedCosts α B ∨ RawExactCosts α B 1 1 ∨ RawExactCosts α B 2 2 ∨
      RawExactCosts α B 3 2 ∨ RawExactCosts α B 3 3 ∨ RawExactCosts α B 5 3 := by
  simpa only [rawBlockedCosts_iff, rawExactCosts_iff] using complete x (encodeBasis B)

theorem no_formula_four_raw {α : Type} (x : α) (B : List RawOp) :
    ¬ExactRawFormulaOver α B 4 := by
  intro h
  exact no_formula_four x (encodeBasis B) ((exactRawFormula_iff B 4).1 h)

theorem every_reachable_cost_raw {α : Type} (x : α) (B : List RawOp)
    (ht : ∃ t : RawFormula α, t.allowed B ∧ t.tautology) :
    ∃ f d, f ≤ 5 ∧ d ≤ 3 ∧ f ≠ 4 ∧ RawExactCosts α B f d := by
  obtain ⟨t, ha, ht⟩ := ht
  have hn : ∃ t : Formula α, t.allowed (encodeBasis B) ∧ t.tautology :=
    ⟨t.encode, (t.encode_allowed B).2 ha, t.encode_tautology.2 ht⟩
  obtain ⟨f, d, hf, hd, hn4, hc⟩ := every_reachable_cost x (encodeBasis B) hn
  exact ⟨f, d, hf, hd, hn4, (rawExactCosts_iff B f d).2 hc⟩

theorem shared_equals_depth_raw {α : Type} (x : α) (B : List RawOp) {g d : Nat}
    (hg : ExactRawDagOver α B g) (hd : ExactRawDepthOver α B d) : g = d :=
  shared_equals_depth x (encodeBasis B)
    ((exactRawDag_iff B g).1 hg) ((exactRawDepth_iff B d).1 hd)

theorem shared_equals_dag_depth_raw {α : Type} (x : α) (B : List RawOp) {g d : Nat}
    (hg : ExactRawDagOver α B g) (hd : ExactRawDagDepthOver α B d) : g = d :=
  shared_equals_dag_depth x (encodeBasis B)
    ((exactRawDag_iff B g).1 hg) ((exactRawDagDepth_iff B d).1 hd)

/-! ## Direct quantification over arbitrary mathematical subsets of functions -/

/-- List representation is derived from a predicate, not supplied as a hypothesis. -/
def rawBasisOf (P : RawOp → Prop) : List RawOp :=
  (basisOf (fun h => P (applyOp h))).map applyOp

theorem mem_rawBasisOf (P : RawOp → Prop) (f : RawOp) :
    f ∈ rawBasisOf P ↔ P f := by
  simp only [rawBasisOf, List.mem_map]
  constructor
  · rintro ⟨h, hm, he⟩
    have hp := (mem_basisOf _ h).1 hm
    simpa only [he] using hp
  · intro hf
    exact ⟨encodeTruthTable f, (mem_basisOf _ _).2
      (by simpa only [binaryFunction_bijection.2] using hf), binaryFunction_bijection.2 f⟩

@[simp] theorem encode_rawBasisOf (P : RawOp → Prop) :
    encodeBasis (rawBasisOf P) = basisOf (fun h => P (applyOp h)) := by
  simp only [encodeBasis, rawBasisOf, List.map_map, Function.comp_def,
    encodeTruthTable_applyOp, List.map_id']

def RawFormula.allowedBy {α : Type} (P : RawOp → Prop) : RawFormula α → Prop
  | .leaf _ => True
  | .gate f a b => P f ∧ RawFormula.allowedBy P a ∧ RawFormula.allowedBy P b

def RawDag.AllowedBy (c : RawDag α) (P : RawOp → Prop) : Prop :=
  ∀ i : Fin c.allocated, P (c.label i)

theorem RawFormula.allowed_rawBasisOf_iff {α : Type} (t : RawFormula α)
    (P : RawOp → Prop) : t.allowed (rawBasisOf P) ↔ RawFormula.allowedBy P t := by
  induction t with
  | leaf x => rfl
  | gate f a b ia ib =>
    simp only [FIG22.Basis.RawFormula.allowed, RawFormula.allowedBy, mem_rawBasisOf, ia, ib]

theorem RawDag.allowed_rawBasisOf_iff (c : RawDag α) (P : RawOp → Prop) :
    c.Allowed (rawBasisOf P) ↔ RawDag.AllowedBy c P := by
  simp only [FIG22.Basis.RawDag.Allowed, RawDag.AllowedBy, mem_rawBasisOf]

def ExactRawFormulaBy (α : Type) (P : RawOp → Prop) (n : Nat) : Prop :=
  (∃ t : RawFormula α, RawFormula.allowedBy P t ∧ t.tautology ∧ t.size = n) ∧
  ∀ t : RawFormula α, RawFormula.allowedBy P t → t.tautology → n ≤ t.size

def ExactRawDepthBy (α : Type) (P : RawOp → Prop) (n : Nat) : Prop :=
  (∃ t : RawFormula α, RawFormula.allowedBy P t ∧ t.tautology ∧ t.depth = n) ∧
  ∀ t : RawFormula α, RawFormula.allowedBy P t → t.tautology → n ≤ t.depth

def ExactRawDagBy (α : Type) (P : RawOp → Prop) (n : Nat) : Prop :=
  (∃ c : RawDag α, RawDag.AllowedBy c P ∧ c.IsTrue ∧ c.reachableCount = n) ∧
  ∀ c : RawDag α, RawDag.AllowedBy c P → c.IsTrue → n ≤ c.reachableCount

def ExactRawDagDepthBy (α : Type) (P : RawOp → Prop) (n : Nat) : Prop :=
  (∃ c : RawDag α, RawDag.AllowedBy c P ∧ c.IsTrue ∧ c.depth = n) ∧
  ∀ c : RawDag α, RawDag.AllowedBy c P → c.IsTrue → n ≤ c.depth

def RawExactCostsBy (α : Type) (P : RawOp → Prop) (f d : Nat) : Prop :=
  ExactRawFormulaBy α P f ∧ ExactRawDagBy α P d ∧ ExactRawDepthBy α P d ∧
    ExactRawDagDepthBy α P d

def RawBlockedCostsBy (α : Type) (P : RawOp → Prop) : Prop :=
  (∀ t : RawFormula α, RawFormula.allowedBy P t → ¬t.tautology) ∧
  (∀ c : RawDag α, RawDag.AllowedBy c P → ¬c.IsTrue)

def RawResultBy (α : Type) (P : RawOp → Prop) : Branch → Prop
  | .one => RawExactCostsBy α P 1 1
  | .noNeg => RawBlockedCostsBy α P
  | .two => RawExactCostsBy α P 2 2
  | .threeTwo => RawExactCostsBy α P 3 2
  | .threeThree => RawExactCostsBy α P 3 3
  | .fiveThree => RawExactCostsBy α P 5 3
  | .final => RawBlockedCostsBy α P

theorem rawExactCostsBy_iff {α : Type} (P : RawOp → Prop) (f d : Nat) :
    RawExactCostsBy α P f d ↔ RawExactCosts α (rawBasisOf P) f d := by
  simp only [RawExactCostsBy, RawExactCosts, ExactRawFormulaBy, ExactRawFormulaOver,
    ExactRawDepthBy, ExactRawDepthOver, ExactRawDagBy, ExactRawDagOver,
    ExactRawDagDepthBy, ExactRawDagDepthOver, RawFormula.allowed_rawBasisOf_iff,
    RawDag.allowed_rawBasisOf_iff]

theorem rawBlockedCostsBy_iff {α : Type} (P : RawOp → Prop) :
    RawBlockedCostsBy α P ↔ RawBlockedCosts α (rawBasisOf P) := by
  simp only [RawBlockedCostsBy, RawBlockedCosts, RawFormula.allowed_rawBasisOf_iff,
    RawDag.allowed_rawBasisOf_iff]

theorem rawResultBy_iff {α : Type} (P : RawOp → Prop) (b : Branch) :
    RawResultBy α P b ↔ RawResult α (rawBasisOf P) b := by
  cases b <;> simp only [RawResultBy, RawResult, rawExactCostsBy_iff, rawBlockedCostsBy_iff]

/-- Every predicate-defined subset of all total binary Boolean functions is covered. -/
theorem theorem_two_raw_subset {α : Type} (x : α) (P : RawOp → Prop) :
    RawResultBy α P (classify (basisOf (fun h => P (applyOp h)))) := by
  have h := theorem_two_raw x (rawBasisOf P)
  rw [encode_rawBasisOf] at h
  exact (rawResultBy_iff P _).2 h

end
end FIG22.Basis.TheoremTwo
