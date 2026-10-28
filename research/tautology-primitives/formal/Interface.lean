import TreeProofs
import DagProofs
import BasisCertificates
import BasisDag

/-!
Agreement of the separately formalized singleton and full-basis interfaces.
No input names or source identities are merged by these operation mappings.
-/
namespace FIG22.Checked

def asDagOp : Tree.Op → DAG.Op
  | .nor => .nor
  | .nand => .nand
  | .xnor => .xnor
  | .implies => .xImpliesY
  | .revImplies => .yImpliesX
  | .top => .binaryTrue

def asBinaryOp : Tree.Op → Basis.Op
  | .nor => 8
  | .nand => 14
  | .xnor => 9
  | .implies => 13
  | .revImplies => 11
  | .top => 15

theorem tree_dag_semantics (op : Tree.Op) (a b : Bool) :
    Tree.apply op a b = (asDagOp op).apply a b := by
  cases op <;> rfl

theorem tree_basis_semantics (op : Tree.Op) (a b : Bool) :
    Tree.apply op a b = Basis.applyOp (asBinaryOp op) a b := by
  cases op <;> cases a <;> cases b <;> decide

theorem shared_depth_cost_agreement (op : Tree.Op) :
    DAG.minimumCost (asDagOp op) = Tree.depthCost op := by
  cases op <;> rfl

/-- One theorem exposes the six singleton tree/depth and reachable-DAG minima. -/
theorem singleton_exact (op : Tree.Op) (n : Nat) (hn : 0 < n) :
    ((∀ t : Tree.Term op n, Tree.Tautology t → Tree.formulaCost op ≤ Tree.size t) ∧
     (∀ t : Tree.Term op n, Tree.Tautology t → Tree.depthCost op ≤ Tree.depth t) ∧
     (∃ t : Tree.Term op n, Tree.Tautology t ∧ Tree.size t = Tree.formulaCost op ∧
       Tree.depth t = Tree.depthCost op)) ∧
    DAG.HasMinimum n (asDagOp op) (Tree.depthCost op) := by
  constructor
  · exact Tree.singleton_minima op n hn
  · rw [← shared_depth_cost_agreement]
    exact DAG.singleton_minimum (asDagOp op) ⟨0, hn⟩

/-- State the depth optimum directly over DAGs, in addition to formula depth. -/
def ExactDagDepthOver (α : Type) (B : List Basis.Op) (d : Nat) : Prop :=
  (∃ c : Basis.Dag α, c.Allowed B ∧ c.IsTrue ∧ c.depth = d) ∧
  ∀ c : Basis.Dag α, c.Allowed B → c.IsTrue → d ≤ c.depth

theorem dag_depth_exact_of_formula_depth
    {α : Type} {B : List Basis.Op} {d : Nat}
    (hf : Basis.ExactDepthOver α B d) (hg : Basis.ExactDagOver α B d) :
    ExactDagDepthOver α B d := by
  have lower (c : Basis.Dag α) (ha : c.Allowed B) (ht : c.IsTrue) :
      d ≤ c.depth := by
    exact hf.2 c.formula (c.unfold_allowed ha (Nat.le_refl _) c.output) ht
  constructor
  · obtain ⟨c, ha, ht, hcost⟩ := hg.1
    have upper : c.depth ≤ d := by
      simpa only [hcost] using c.depth_le_reachable
    exact ⟨c, ha, ht, Nat.le_antisymm upper (lower c ha ht)⟩
  · exact lower

theorem every_generating_row_dag_depth {α : Type} (x : α) {r : Basis.Row}
    (hm : r ∈ Basis.rows) (hg : r.generates = true) :
    ExactDagDepthOver α r.basis r.depthCost := by
  have h := Basis.every_generating_row_all_costs x hm hg
  exact dag_depth_exact_of_formula_depth h.2.2 h.2.1

end FIG22.Checked
