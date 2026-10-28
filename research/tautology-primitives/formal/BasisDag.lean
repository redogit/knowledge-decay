import BasisCertificates

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

theorem row000_dag_blocked (c : Dag α) (ha : c.Allowed row000.basis) :
    ¬c.IsTrue := c.blocked_of_formula row000_blocked ha

theorem row001_dag_blocked (c : Dag α) (ha : c.Allowed row001.basis) :
    ¬c.IsTrue := c.blocked_of_formula row001_blocked ha

theorem row002_dag_blocked (c : Dag α) (ha : c.Allowed row002.basis) :
    ¬c.IsTrue := c.blocked_of_formula row002_blocked ha

theorem row003_dag_blocked (c : Dag α) (ha : c.Allowed row003.basis) :
    ¬c.IsTrue := c.blocked_of_formula row003_blocked ha

theorem row004_dag_blocked (c : Dag α) (ha : c.Allowed row004.basis) :
    ¬c.IsTrue := c.blocked_of_formula row004_blocked ha

theorem row005_dag_blocked (c : Dag α) (ha : c.Allowed row005.basis) :
    ¬c.IsTrue := c.blocked_of_formula row005_blocked ha

theorem row006_dag_blocked (c : Dag α) (ha : c.Allowed row006.basis) :
    ¬c.IsTrue := c.blocked_of_formula row006_blocked ha

theorem row007_dag_blocked (c : Dag α) (ha : c.Allowed row007.basis) :
    ¬c.IsTrue := c.blocked_of_formula row007_blocked ha

-- 8: NOR; reachable DAG cost 3
def dag008 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 8 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag008_allowed (x : α) : (dag008 x).Allowed row008.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag008, row008, h]

theorem dag008_true (x : α) : (dag008 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag008, applyOp, hv] <;> decide

theorem dag008_cost (x : α) : (dag008 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag008]
  decide

theorem row008_dag_exact (x : α) : ExactDagOver α row008.basis 3 := by
  constructor
  · exact ⟨dag008 x, dag008_allowed x, dag008_true x, dag008_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row008_exact.2 ha ht

-- 9: XNOR; reachable DAG cost 1
def dag009 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag009_allowed (x : α) : (dag009 x).Allowed row009.basis := by
  intro i
  simp [dag009, row009]

theorem dag009_true (x : α) : (dag009 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag009, applyOp, hv] <;> decide

theorem dag009_cost (x : α) : (dag009 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag009]
  decide

theorem row009_dag_exact (x : α) : ExactDagOver α row009.basis 1 := by
  constructor
  · exact ⟨dag009 x, dag009_allowed x, dag009_true x, dag009_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row009_exact.2 ha ht

theorem row010_dag_blocked (c : Dag α) (ha : c.Allowed row010.basis) :
    ¬c.IsTrue := c.blocked_of_formula row010_blocked ha

-- 11: Y_IMPLIES_X; reachable DAG cost 1
def dag011 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag011_allowed (x : α) : (dag011 x).Allowed row011.basis := by
  intro i
  simp [dag011, row011]

theorem dag011_true (x : α) : (dag011 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag011, applyOp, hv] <;> decide

theorem dag011_cost (x : α) : (dag011 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag011]
  decide

theorem row011_dag_exact (x : α) : ExactDagOver α row011.basis 1 := by
  constructor
  · exact ⟨dag011 x, dag011_allowed x, dag011_true x, dag011_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row011_exact.2 ha ht

theorem row012_dag_blocked (c : Dag α) (ha : c.Allowed row012.basis) :
    ¬c.IsTrue := c.blocked_of_formula row012_blocked ha

-- 13: X_IMPLIES_Y; reachable DAG cost 1
def dag013 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag013_allowed (x : α) : (dag013 x).Allowed row013.basis := by
  intro i
  simp [dag013, row013]

theorem dag013_true (x : α) : (dag013 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag013, applyOp, hv] <;> decide

theorem dag013_cost (x : α) : (dag013 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag013]
  decide

theorem row013_dag_exact (x : α) : ExactDagOver α row013.basis 1 := by
  constructor
  · exact ⟨dag013 x, dag013_allowed x, dag013_true x, dag013_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row013_exact.2 ha ht

-- 14: NAND; reachable DAG cost 2
def dag014 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 14 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag014_allowed (x : α) : (dag014 x).Allowed row014.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag014, row014, h]

theorem dag014_true (x : α) : (dag014 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag014, applyOp, hv] <;> decide

theorem dag014_cost (x : α) : (dag014 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag014]
  decide

theorem row014_dag_exact (x : α) : ExactDagOver α row014.basis 2 := by
  constructor
  · exact ⟨dag014 x, dag014_allowed x, dag014_true x, dag014_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row014_exact.2 ha ht

-- 15: TRUE; reachable DAG cost 1
def dag015 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag015_allowed (x : α) : (dag015 x).Allowed row015.basis := by
  intro i
  simp [dag015, row015]

theorem dag015_true (x : α) : (dag015 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag015, applyOp, hv] <;> decide

theorem dag015_cost (x : α) : (dag015 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag015]
  decide

theorem row015_dag_exact (x : α) : ExactDagOver α row015.basis 1 := by
  constructor
  · exact ⟨dag015 x, dag015_allowed x, dag015_true x, dag015_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row015_exact.2 ha ht

theorem row016_dag_blocked (c : Dag α) (ha : c.Allowed row016.basis) :
    ¬c.IsTrue := c.blocked_of_formula row016_blocked ha

theorem row017_dag_blocked (c : Dag α) (ha : c.Allowed row017.basis) :
    ¬c.IsTrue := c.blocked_of_formula row017_blocked ha

theorem row018_dag_blocked (c : Dag α) (ha : c.Allowed row018.basis) :
    ¬c.IsTrue := c.blocked_of_formula row018_blocked ha

theorem row019_dag_blocked (c : Dag α) (ha : c.Allowed row019.basis) :
    ¬c.IsTrue := c.blocked_of_formula row019_blocked ha

theorem row020_dag_blocked (c : Dag α) (ha : c.Allowed row020.basis) :
    ¬c.IsTrue := c.blocked_of_formula row020_blocked ha

theorem row021_dag_blocked (c : Dag α) (ha : c.Allowed row021.basis) :
    ¬c.IsTrue := c.blocked_of_formula row021_blocked ha

theorem row022_dag_blocked (c : Dag α) (ha : c.Allowed row022.basis) :
    ¬c.IsTrue := c.blocked_of_formula row022_blocked ha

-- 23: FALSE, NOR; reachable DAG cost 2
def dag023 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 0 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag023_allowed (x : α) : (dag023 x).Allowed row023.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag023, row023, h]

theorem dag023_true (x : α) : (dag023 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag023, applyOp, hv] <;> decide

theorem dag023_cost (x : α) : (dag023 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag023]
  decide

theorem row023_dag_exact (x : α) : ExactDagOver α row023.basis 2 := by
  constructor
  · exact ⟨dag023 x, dag023_allowed x, dag023_true x, dag023_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row023_exact.2 ha ht

-- 24: FALSE, XNOR; reachable DAG cost 1
def dag024 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag024_allowed (x : α) : (dag024 x).Allowed row024.basis := by
  intro i
  simp [dag024, row024]

theorem dag024_true (x : α) : (dag024 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag024, applyOp, hv] <;> decide

theorem dag024_cost (x : α) : (dag024 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag024]
  decide

theorem row024_dag_exact (x : α) : ExactDagOver α row024.basis 1 := by
  constructor
  · exact ⟨dag024 x, dag024_allowed x, dag024_true x, dag024_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row024_exact.2 ha ht

-- 25: FALSE, NOT_Y; reachable DAG cost 2
def dag025 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 0 else 10
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag025_allowed (x : α) : (dag025 x).Allowed row025.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag025, row025, h]

theorem dag025_true (x : α) : (dag025 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag025, applyOp, hv] <;> decide

theorem dag025_cost (x : α) : (dag025 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag025]
  decide

theorem row025_dag_exact (x : α) : ExactDagOver α row025.basis 2 := by
  constructor
  · exact ⟨dag025 x, dag025_allowed x, dag025_true x, dag025_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row025_exact.2 ha ht

-- 26: FALSE, Y_IMPLIES_X; reachable DAG cost 1
def dag026 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag026_allowed (x : α) : (dag026 x).Allowed row026.basis := by
  intro i
  simp [dag026, row026]

theorem dag026_true (x : α) : (dag026 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag026, applyOp, hv] <;> decide

theorem dag026_cost (x : α) : (dag026 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag026]
  decide

theorem row026_dag_exact (x : α) : ExactDagOver α row026.basis 1 := by
  constructor
  · exact ⟨dag026 x, dag026_allowed x, dag026_true x, dag026_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row026_exact.2 ha ht

-- 27: FALSE, NOT_X; reachable DAG cost 2
def dag027 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 0 else 12
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag027_allowed (x : α) : (dag027 x).Allowed row027.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag027, row027, h]

theorem dag027_true (x : α) : (dag027 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag027, applyOp, hv] <;> decide

theorem dag027_cost (x : α) : (dag027 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag027]
  decide

theorem row027_dag_exact (x : α) : ExactDagOver α row027.basis 2 := by
  constructor
  · exact ⟨dag027 x, dag027_allowed x, dag027_true x, dag027_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row027_exact.2 ha ht

-- 28: FALSE, X_IMPLIES_Y; reachable DAG cost 1
def dag028 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag028_allowed (x : α) : (dag028 x).Allowed row028.basis := by
  intro i
  simp [dag028, row028]

theorem dag028_true (x : α) : (dag028 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag028, applyOp, hv] <;> decide

theorem dag028_cost (x : α) : (dag028 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag028]
  decide

theorem row028_dag_exact (x : α) : ExactDagOver α row028.basis 1 := by
  constructor
  · exact ⟨dag028 x, dag028_allowed x, dag028_true x, dag028_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row028_exact.2 ha ht

-- 29: FALSE, NAND; reachable DAG cost 2
def dag029 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 0 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag029_allowed (x : α) : (dag029 x).Allowed row029.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag029, row029, h]

theorem dag029_true (x : α) : (dag029 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag029, applyOp, hv] <;> decide

theorem dag029_cost (x : α) : (dag029 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag029]
  decide

theorem row029_dag_exact (x : α) : ExactDagOver α row029.basis 2 := by
  constructor
  · exact ⟨dag029 x, dag029_allowed x, dag029_true x, dag029_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row029_exact.2 ha ht

-- 30: FALSE, TRUE; reachable DAG cost 1
def dag030 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag030_allowed (x : α) : (dag030 x).Allowed row030.basis := by
  intro i
  simp [dag030, row030]

theorem dag030_true (x : α) : (dag030 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag030, applyOp, hv] <;> decide

theorem dag030_cost (x : α) : (dag030 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag030]
  decide

theorem row030_dag_exact (x : α) : ExactDagOver α row030.basis 1 := by
  constructor
  · exact ⟨dag030 x, dag030_allowed x, dag030_true x, dag030_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row030_exact.2 ha ht

theorem row031_dag_blocked (c : Dag α) (ha : c.Allowed row031.basis) :
    ¬c.IsTrue := c.blocked_of_formula row031_blocked ha

theorem row032_dag_blocked (c : Dag α) (ha : c.Allowed row032.basis) :
    ¬c.IsTrue := c.blocked_of_formula row032_blocked ha

theorem row033_dag_blocked (c : Dag α) (ha : c.Allowed row033.basis) :
    ¬c.IsTrue := c.blocked_of_formula row033_blocked ha

theorem row034_dag_blocked (c : Dag α) (ha : c.Allowed row034.basis) :
    ¬c.IsTrue := c.blocked_of_formula row034_blocked ha

theorem row035_dag_blocked (c : Dag α) (ha : c.Allowed row035.basis) :
    ¬c.IsTrue := c.blocked_of_formula row035_blocked ha

theorem row036_dag_blocked (c : Dag α) (ha : c.Allowed row036.basis) :
    ¬c.IsTrue := c.blocked_of_formula row036_blocked ha

-- 37: AND, NOR; reachable DAG cost 3
def dag037 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 1 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag037_allowed (x : α) : (dag037 x).Allowed row037.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag037, row037, h]

theorem dag037_true (x : α) : (dag037 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag037, applyOp, hv] <;> decide

theorem dag037_cost (x : α) : (dag037 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag037]
  decide

theorem row037_dag_exact (x : α) : ExactDagOver α row037.basis 3 := by
  constructor
  · exact ⟨dag037 x, dag037_allowed x, dag037_true x, dag037_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row037_exact.2 ha ht

-- 38: AND, XNOR; reachable DAG cost 1
def dag038 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag038_allowed (x : α) : (dag038 x).Allowed row038.basis := by
  intro i
  simp [dag038, row038]

theorem dag038_true (x : α) : (dag038 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag038, applyOp, hv] <;> decide

theorem dag038_cost (x : α) : (dag038 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag038]
  decide

theorem row038_dag_exact (x : α) : ExactDagOver α row038.basis 1 := by
  constructor
  · exact ⟨dag038 x, dag038_allowed x, dag038_true x, dag038_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row038_exact.2 ha ht

-- 39: AND, NOT_Y; reachable DAG cost 3
def dag039 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 10 else if i.val = 1 then 1 else 10
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag039_allowed (x : α) : (dag039 x).Allowed row039.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag039, row039, h]

theorem dag039_true (x : α) : (dag039 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag039, applyOp, hv] <;> decide

theorem dag039_cost (x : α) : (dag039 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag039]
  decide

theorem row039_dag_exact (x : α) : ExactDagOver α row039.basis 3 := by
  constructor
  · exact ⟨dag039 x, dag039_allowed x, dag039_true x, dag039_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row039_exact.2 ha ht

-- 40: AND, Y_IMPLIES_X; reachable DAG cost 1
def dag040 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag040_allowed (x : α) : (dag040 x).Allowed row040.basis := by
  intro i
  simp [dag040, row040]

theorem dag040_true (x : α) : (dag040 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag040, applyOp, hv] <;> decide

theorem dag040_cost (x : α) : (dag040 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag040]
  decide

theorem row040_dag_exact (x : α) : ExactDagOver α row040.basis 1 := by
  constructor
  · exact ⟨dag040 x, dag040_allowed x, dag040_true x, dag040_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row040_exact.2 ha ht

-- 41: AND, NOT_X; reachable DAG cost 3
def dag041 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 12 else if i.val = 1 then 1 else 12
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag041_allowed (x : α) : (dag041 x).Allowed row041.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag041, row041, h]

theorem dag041_true (x : α) : (dag041 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag041, applyOp, hv] <;> decide

theorem dag041_cost (x : α) : (dag041 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag041]
  decide

theorem row041_dag_exact (x : α) : ExactDagOver α row041.basis 3 := by
  constructor
  · exact ⟨dag041 x, dag041_allowed x, dag041_true x, dag041_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row041_exact.2 ha ht

-- 42: AND, X_IMPLIES_Y; reachable DAG cost 1
def dag042 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag042_allowed (x : α) : (dag042 x).Allowed row042.basis := by
  intro i
  simp [dag042, row042]

theorem dag042_true (x : α) : (dag042 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag042, applyOp, hv] <;> decide

theorem dag042_cost (x : α) : (dag042 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag042]
  decide

theorem row042_dag_exact (x : α) : ExactDagOver α row042.basis 1 := by
  constructor
  · exact ⟨dag042 x, dag042_allowed x, dag042_true x, dag042_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row042_exact.2 ha ht

-- 43: AND, NAND; reachable DAG cost 2
def dag043 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 14 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag043_allowed (x : α) : (dag043 x).Allowed row043.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag043, row043, h]

theorem dag043_true (x : α) : (dag043 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag043, applyOp, hv] <;> decide

theorem dag043_cost (x : α) : (dag043 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag043]
  decide

theorem row043_dag_exact (x : α) : ExactDagOver α row043.basis 2 := by
  constructor
  · exact ⟨dag043 x, dag043_allowed x, dag043_true x, dag043_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row043_exact.2 ha ht

-- 44: AND, TRUE; reachable DAG cost 1
def dag044 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag044_allowed (x : α) : (dag044 x).Allowed row044.basis := by
  intro i
  simp [dag044, row044]

theorem dag044_true (x : α) : (dag044 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag044, applyOp, hv] <;> decide

theorem dag044_cost (x : α) : (dag044 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag044]
  decide

theorem row044_dag_exact (x : α) : ExactDagOver α row044.basis 1 := by
  constructor
  · exact ⟨dag044 x, dag044_allowed x, dag044_true x, dag044_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row044_exact.2 ha ht

theorem row045_dag_blocked (c : Dag α) (ha : c.Allowed row045.basis) :
    ¬c.IsTrue := c.blocked_of_formula row045_blocked ha

theorem row046_dag_blocked (c : Dag α) (ha : c.Allowed row046.basis) :
    ¬c.IsTrue := c.blocked_of_formula row046_blocked ha

theorem row047_dag_blocked (c : Dag α) (ha : c.Allowed row047.basis) :
    ¬c.IsTrue := c.blocked_of_formula row047_blocked ha

theorem row048_dag_blocked (c : Dag α) (ha : c.Allowed row048.basis) :
    ¬c.IsTrue := c.blocked_of_formula row048_blocked ha

theorem row049_dag_blocked (c : Dag α) (ha : c.Allowed row049.basis) :
    ¬c.IsTrue := c.blocked_of_formula row049_blocked ha

-- 50: X_AND_NOT_Y, NOR; reachable DAG cost 2
def dag050 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 2 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag050_allowed (x : α) : (dag050 x).Allowed row050.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag050, row050, h]

theorem dag050_true (x : α) : (dag050 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag050, applyOp, hv] <;> decide

theorem dag050_cost (x : α) : (dag050 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag050]
  decide

theorem row050_dag_exact (x : α) : ExactDagOver α row050.basis 2 := by
  constructor
  · exact ⟨dag050 x, dag050_allowed x, dag050_true x, dag050_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row050_exact.2 ha ht

-- 51: X_AND_NOT_Y, XNOR; reachable DAG cost 1
def dag051 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag051_allowed (x : α) : (dag051 x).Allowed row051.basis := by
  intro i
  simp [dag051, row051]

theorem dag051_true (x : α) : (dag051 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag051, applyOp, hv] <;> decide

theorem dag051_cost (x : α) : (dag051 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag051]
  decide

theorem row051_dag_exact (x : α) : ExactDagOver α row051.basis 1 := by
  constructor
  · exact ⟨dag051 x, dag051_allowed x, dag051_true x, dag051_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row051_exact.2 ha ht

-- 52: X_AND_NOT_Y, NOT_Y; reachable DAG cost 2
def dag052 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 2 else 10
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag052_allowed (x : α) : (dag052 x).Allowed row052.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag052, row052, h]

theorem dag052_true (x : α) : (dag052 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag052, applyOp, hv] <;> decide

theorem dag052_cost (x : α) : (dag052 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag052]
  decide

theorem row052_dag_exact (x : α) : ExactDagOver α row052.basis 2 := by
  constructor
  · exact ⟨dag052 x, dag052_allowed x, dag052_true x, dag052_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row052_exact.2 ha ht

-- 53: X_AND_NOT_Y, Y_IMPLIES_X; reachable DAG cost 1
def dag053 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag053_allowed (x : α) : (dag053 x).Allowed row053.basis := by
  intro i
  simp [dag053, row053]

theorem dag053_true (x : α) : (dag053 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag053, applyOp, hv] <;> decide

theorem dag053_cost (x : α) : (dag053 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag053]
  decide

theorem row053_dag_exact (x : α) : ExactDagOver α row053.basis 1 := by
  constructor
  · exact ⟨dag053 x, dag053_allowed x, dag053_true x, dag053_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row053_exact.2 ha ht

-- 54: X_AND_NOT_Y, NOT_X; reachable DAG cost 2
def dag054 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 2 else 12
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag054_allowed (x : α) : (dag054 x).Allowed row054.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag054, row054, h]

theorem dag054_true (x : α) : (dag054 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag054, applyOp, hv] <;> decide

theorem dag054_cost (x : α) : (dag054 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag054]
  decide

theorem row054_dag_exact (x : α) : ExactDagOver α row054.basis 2 := by
  constructor
  · exact ⟨dag054 x, dag054_allowed x, dag054_true x, dag054_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row054_exact.2 ha ht

-- 55: X_AND_NOT_Y, X_IMPLIES_Y; reachable DAG cost 1
def dag055 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag055_allowed (x : α) : (dag055 x).Allowed row055.basis := by
  intro i
  simp [dag055, row055]

theorem dag055_true (x : α) : (dag055 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag055, applyOp, hv] <;> decide

theorem dag055_cost (x : α) : (dag055 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag055]
  decide

theorem row055_dag_exact (x : α) : ExactDagOver α row055.basis 1 := by
  constructor
  · exact ⟨dag055 x, dag055_allowed x, dag055_true x, dag055_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row055_exact.2 ha ht

-- 56: X_AND_NOT_Y, NAND; reachable DAG cost 2
def dag056 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 2 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag056_allowed (x : α) : (dag056 x).Allowed row056.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag056, row056, h]

theorem dag056_true (x : α) : (dag056 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag056, applyOp, hv] <;> decide

theorem dag056_cost (x : α) : (dag056 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag056]
  decide

theorem row056_dag_exact (x : α) : ExactDagOver α row056.basis 2 := by
  constructor
  · exact ⟨dag056 x, dag056_allowed x, dag056_true x, dag056_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row056_exact.2 ha ht

-- 57: X_AND_NOT_Y, TRUE; reachable DAG cost 1
def dag057 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag057_allowed (x : α) : (dag057 x).Allowed row057.basis := by
  intro i
  simp [dag057, row057]

theorem dag057_true (x : α) : (dag057 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag057, applyOp, hv] <;> decide

theorem dag057_cost (x : α) : (dag057 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag057]
  decide

theorem row057_dag_exact (x : α) : ExactDagOver α row057.basis 1 := by
  constructor
  · exact ⟨dag057 x, dag057_allowed x, dag057_true x, dag057_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row057_exact.2 ha ht

theorem row058_dag_blocked (c : Dag α) (ha : c.Allowed row058.basis) :
    ¬c.IsTrue := c.blocked_of_formula row058_blocked ha

theorem row059_dag_blocked (c : Dag α) (ha : c.Allowed row059.basis) :
    ¬c.IsTrue := c.blocked_of_formula row059_blocked ha

theorem row060_dag_blocked (c : Dag α) (ha : c.Allowed row060.basis) :
    ¬c.IsTrue := c.blocked_of_formula row060_blocked ha

theorem row061_dag_blocked (c : Dag α) (ha : c.Allowed row061.basis) :
    ¬c.IsTrue := c.blocked_of_formula row061_blocked ha

-- 62: X, NOR; reachable DAG cost 3
def dag062 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 8 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag062_allowed (x : α) : (dag062 x).Allowed row062.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag062, row062, h]

theorem dag062_true (x : α) : (dag062 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag062, applyOp, hv] <;> decide

theorem dag062_cost (x : α) : (dag062 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag062]
  decide

theorem row062_dag_exact (x : α) : ExactDagOver α row062.basis 3 := by
  constructor
  · exact ⟨dag062 x, dag062_allowed x, dag062_true x, dag062_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row062_exact.2 ha ht

-- 63: X, XNOR; reachable DAG cost 1
def dag063 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag063_allowed (x : α) : (dag063 x).Allowed row063.basis := by
  intro i
  simp [dag063, row063]

theorem dag063_true (x : α) : (dag063 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag063, applyOp, hv] <;> decide

theorem dag063_cost (x : α) : (dag063 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag063]
  decide

theorem row063_dag_exact (x : α) : ExactDagOver α row063.basis 1 := by
  constructor
  · exact ⟨dag063 x, dag063_allowed x, dag063_true x, dag063_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row063_exact.2 ha ht

theorem row064_dag_blocked (c : Dag α) (ha : c.Allowed row064.basis) :
    ¬c.IsTrue := c.blocked_of_formula row064_blocked ha

-- 65: X, Y_IMPLIES_X; reachable DAG cost 1
def dag065 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag065_allowed (x : α) : (dag065 x).Allowed row065.basis := by
  intro i
  simp [dag065, row065]

theorem dag065_true (x : α) : (dag065 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag065, applyOp, hv] <;> decide

theorem dag065_cost (x : α) : (dag065 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag065]
  decide

theorem row065_dag_exact (x : α) : ExactDagOver α row065.basis 1 := by
  constructor
  · exact ⟨dag065 x, dag065_allowed x, dag065_true x, dag065_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row065_exact.2 ha ht

theorem row066_dag_blocked (c : Dag α) (ha : c.Allowed row066.basis) :
    ¬c.IsTrue := c.blocked_of_formula row066_blocked ha

-- 67: X, X_IMPLIES_Y; reachable DAG cost 1
def dag067 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag067_allowed (x : α) : (dag067 x).Allowed row067.basis := by
  intro i
  simp [dag067, row067]

theorem dag067_true (x : α) : (dag067 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag067, applyOp, hv] <;> decide

theorem dag067_cost (x : α) : (dag067 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag067]
  decide

theorem row067_dag_exact (x : α) : ExactDagOver α row067.basis 1 := by
  constructor
  · exact ⟨dag067 x, dag067_allowed x, dag067_true x, dag067_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row067_exact.2 ha ht

-- 68: X, NAND; reachable DAG cost 2
def dag068 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 14 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag068_allowed (x : α) : (dag068 x).Allowed row068.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag068, row068, h]

theorem dag068_true (x : α) : (dag068 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag068, applyOp, hv] <;> decide

theorem dag068_cost (x : α) : (dag068 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag068]
  decide

theorem row068_dag_exact (x : α) : ExactDagOver α row068.basis 2 := by
  constructor
  · exact ⟨dag068 x, dag068_allowed x, dag068_true x, dag068_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row068_exact.2 ha ht

-- 69: X, TRUE; reachable DAG cost 1
def dag069 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag069_allowed (x : α) : (dag069 x).Allowed row069.basis := by
  intro i
  simp [dag069, row069]

theorem dag069_true (x : α) : (dag069 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag069, applyOp, hv] <;> decide

theorem dag069_cost (x : α) : (dag069 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag069]
  decide

theorem row069_dag_exact (x : α) : ExactDagOver α row069.basis 1 := by
  constructor
  · exact ⟨dag069 x, dag069_allowed x, dag069_true x, dag069_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row069_exact.2 ha ht

theorem row070_dag_blocked (c : Dag α) (ha : c.Allowed row070.basis) :
    ¬c.IsTrue := c.blocked_of_formula row070_blocked ha

theorem row071_dag_blocked (c : Dag α) (ha : c.Allowed row071.basis) :
    ¬c.IsTrue := c.blocked_of_formula row071_blocked ha

theorem row072_dag_blocked (c : Dag α) (ha : c.Allowed row072.basis) :
    ¬c.IsTrue := c.blocked_of_formula row072_blocked ha

-- 73: NOT_X_AND_Y, NOR; reachable DAG cost 2
def dag073 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 4 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag073_allowed (x : α) : (dag073 x).Allowed row073.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag073, row073, h]

theorem dag073_true (x : α) : (dag073 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag073, applyOp, hv] <;> decide

theorem dag073_cost (x : α) : (dag073 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag073]
  decide

theorem row073_dag_exact (x : α) : ExactDagOver α row073.basis 2 := by
  constructor
  · exact ⟨dag073 x, dag073_allowed x, dag073_true x, dag073_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row073_exact.2 ha ht

-- 74: NOT_X_AND_Y, XNOR; reachable DAG cost 1
def dag074 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag074_allowed (x : α) : (dag074 x).Allowed row074.basis := by
  intro i
  simp [dag074, row074]

theorem dag074_true (x : α) : (dag074 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag074, applyOp, hv] <;> decide

theorem dag074_cost (x : α) : (dag074 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag074]
  decide

theorem row074_dag_exact (x : α) : ExactDagOver α row074.basis 1 := by
  constructor
  · exact ⟨dag074 x, dag074_allowed x, dag074_true x, dag074_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row074_exact.2 ha ht

-- 75: NOT_X_AND_Y, NOT_Y; reachable DAG cost 2
def dag075 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 4 else 10
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag075_allowed (x : α) : (dag075 x).Allowed row075.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag075, row075, h]

theorem dag075_true (x : α) : (dag075 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag075, applyOp, hv] <;> decide

theorem dag075_cost (x : α) : (dag075 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag075]
  decide

theorem row075_dag_exact (x : α) : ExactDagOver α row075.basis 2 := by
  constructor
  · exact ⟨dag075 x, dag075_allowed x, dag075_true x, dag075_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row075_exact.2 ha ht

-- 76: NOT_X_AND_Y, Y_IMPLIES_X; reachable DAG cost 1
def dag076 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag076_allowed (x : α) : (dag076 x).Allowed row076.basis := by
  intro i
  simp [dag076, row076]

theorem dag076_true (x : α) : (dag076 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag076, applyOp, hv] <;> decide

theorem dag076_cost (x : α) : (dag076 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag076]
  decide

theorem row076_dag_exact (x : α) : ExactDagOver α row076.basis 1 := by
  constructor
  · exact ⟨dag076 x, dag076_allowed x, dag076_true x, dag076_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row076_exact.2 ha ht

-- 77: NOT_X_AND_Y, NOT_X; reachable DAG cost 2
def dag077 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 4 else 12
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag077_allowed (x : α) : (dag077 x).Allowed row077.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag077, row077, h]

theorem dag077_true (x : α) : (dag077 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag077, applyOp, hv] <;> decide

theorem dag077_cost (x : α) : (dag077 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag077]
  decide

theorem row077_dag_exact (x : α) : ExactDagOver α row077.basis 2 := by
  constructor
  · exact ⟨dag077 x, dag077_allowed x, dag077_true x, dag077_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row077_exact.2 ha ht

-- 78: NOT_X_AND_Y, X_IMPLIES_Y; reachable DAG cost 1
def dag078 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag078_allowed (x : α) : (dag078 x).Allowed row078.basis := by
  intro i
  simp [dag078, row078]

theorem dag078_true (x : α) : (dag078 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag078, applyOp, hv] <;> decide

theorem dag078_cost (x : α) : (dag078 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag078]
  decide

theorem row078_dag_exact (x : α) : ExactDagOver α row078.basis 1 := by
  constructor
  · exact ⟨dag078 x, dag078_allowed x, dag078_true x, dag078_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row078_exact.2 ha ht

-- 79: NOT_X_AND_Y, NAND; reachable DAG cost 2
def dag079 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 4 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag079_allowed (x : α) : (dag079 x).Allowed row079.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag079, row079, h]

theorem dag079_true (x : α) : (dag079 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag079, applyOp, hv] <;> decide

theorem dag079_cost (x : α) : (dag079 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag079]
  decide

theorem row079_dag_exact (x : α) : ExactDagOver α row079.basis 2 := by
  constructor
  · exact ⟨dag079 x, dag079_allowed x, dag079_true x, dag079_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row079_exact.2 ha ht

-- 80: NOT_X_AND_Y, TRUE; reachable DAG cost 1
def dag080 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag080_allowed (x : α) : (dag080 x).Allowed row080.basis := by
  intro i
  simp [dag080, row080]

theorem dag080_true (x : α) : (dag080 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag080, applyOp, hv] <;> decide

theorem dag080_cost (x : α) : (dag080 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag080]
  decide

theorem row080_dag_exact (x : α) : ExactDagOver α row080.basis 1 := by
  constructor
  · exact ⟨dag080 x, dag080_allowed x, dag080_true x, dag080_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row080_exact.2 ha ht

theorem row081_dag_blocked (c : Dag α) (ha : c.Allowed row081.basis) :
    ¬c.IsTrue := c.blocked_of_formula row081_blocked ha

theorem row082_dag_blocked (c : Dag α) (ha : c.Allowed row082.basis) :
    ¬c.IsTrue := c.blocked_of_formula row082_blocked ha

-- 83: Y, NOR; reachable DAG cost 3
def dag083 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 8 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag083_allowed (x : α) : (dag083 x).Allowed row083.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag083, row083, h]

theorem dag083_true (x : α) : (dag083 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag083, applyOp, hv] <;> decide

theorem dag083_cost (x : α) : (dag083 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag083]
  decide

theorem row083_dag_exact (x : α) : ExactDagOver α row083.basis 3 := by
  constructor
  · exact ⟨dag083 x, dag083_allowed x, dag083_true x, dag083_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row083_exact.2 ha ht

-- 84: Y, XNOR; reachable DAG cost 1
def dag084 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag084_allowed (x : α) : (dag084 x).Allowed row084.basis := by
  intro i
  simp [dag084, row084]

theorem dag084_true (x : α) : (dag084 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag084, applyOp, hv] <;> decide

theorem dag084_cost (x : α) : (dag084 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag084]
  decide

theorem row084_dag_exact (x : α) : ExactDagOver α row084.basis 1 := by
  constructor
  · exact ⟨dag084 x, dag084_allowed x, dag084_true x, dag084_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row084_exact.2 ha ht

theorem row085_dag_blocked (c : Dag α) (ha : c.Allowed row085.basis) :
    ¬c.IsTrue := c.blocked_of_formula row085_blocked ha

-- 86: Y, Y_IMPLIES_X; reachable DAG cost 1
def dag086 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag086_allowed (x : α) : (dag086 x).Allowed row086.basis := by
  intro i
  simp [dag086, row086]

theorem dag086_true (x : α) : (dag086 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag086, applyOp, hv] <;> decide

theorem dag086_cost (x : α) : (dag086 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag086]
  decide

theorem row086_dag_exact (x : α) : ExactDagOver α row086.basis 1 := by
  constructor
  · exact ⟨dag086 x, dag086_allowed x, dag086_true x, dag086_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row086_exact.2 ha ht

theorem row087_dag_blocked (c : Dag α) (ha : c.Allowed row087.basis) :
    ¬c.IsTrue := c.blocked_of_formula row087_blocked ha

-- 88: Y, X_IMPLIES_Y; reachable DAG cost 1
def dag088 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag088_allowed (x : α) : (dag088 x).Allowed row088.basis := by
  intro i
  simp [dag088, row088]

theorem dag088_true (x : α) : (dag088 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag088, applyOp, hv] <;> decide

theorem dag088_cost (x : α) : (dag088 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag088]
  decide

theorem row088_dag_exact (x : α) : ExactDagOver α row088.basis 1 := by
  constructor
  · exact ⟨dag088 x, dag088_allowed x, dag088_true x, dag088_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row088_exact.2 ha ht

-- 89: Y, NAND; reachable DAG cost 2
def dag089 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 14 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag089_allowed (x : α) : (dag089 x).Allowed row089.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag089, row089, h]

theorem dag089_true (x : α) : (dag089 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag089, applyOp, hv] <;> decide

theorem dag089_cost (x : α) : (dag089 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag089]
  decide

theorem row089_dag_exact (x : α) : ExactDagOver α row089.basis 2 := by
  constructor
  · exact ⟨dag089 x, dag089_allowed x, dag089_true x, dag089_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row089_exact.2 ha ht

-- 90: Y, TRUE; reachable DAG cost 1
def dag090 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag090_allowed (x : α) : (dag090 x).Allowed row090.basis := by
  intro i
  simp [dag090, row090]

theorem dag090_true (x : α) : (dag090 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag090, applyOp, hv] <;> decide

theorem dag090_cost (x : α) : (dag090 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag090]
  decide

theorem row090_dag_exact (x : α) : ExactDagOver α row090.basis 1 := by
  constructor
  · exact ⟨dag090 x, dag090_allowed x, dag090_true x, dag090_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row090_exact.2 ha ht

theorem row091_dag_blocked (c : Dag α) (ha : c.Allowed row091.basis) :
    ¬c.IsTrue := c.blocked_of_formula row091_blocked ha

-- 92: XOR, NOR; reachable DAG cost 2
def dag092 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 6 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag092_allowed (x : α) : (dag092 x).Allowed row092.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag092, row092, h]

theorem dag092_true (x : α) : (dag092 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag092, applyOp, hv] <;> decide

theorem dag092_cost (x : α) : (dag092 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag092]
  decide

theorem row092_dag_exact (x : α) : ExactDagOver α row092.basis 2 := by
  constructor
  · exact ⟨dag092 x, dag092_allowed x, dag092_true x, dag092_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row092_exact.2 ha ht

-- 93: XOR, XNOR; reachable DAG cost 1
def dag093 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag093_allowed (x : α) : (dag093 x).Allowed row093.basis := by
  intro i
  simp [dag093, row093]

theorem dag093_true (x : α) : (dag093 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag093, applyOp, hv] <;> decide

theorem dag093_cost (x : α) : (dag093 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag093]
  decide

theorem row093_dag_exact (x : α) : ExactDagOver α row093.basis 1 := by
  constructor
  · exact ⟨dag093 x, dag093_allowed x, dag093_true x, dag093_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row093_exact.2 ha ht

-- 94: XOR, NOT_Y; reachable DAG cost 2
def dag094 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 6 else 10
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag094_allowed (x : α) : (dag094 x).Allowed row094.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag094, row094, h]

theorem dag094_true (x : α) : (dag094 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag094, applyOp, hv] <;> decide

theorem dag094_cost (x : α) : (dag094 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag094]
  decide

theorem row094_dag_exact (x : α) : ExactDagOver α row094.basis 2 := by
  constructor
  · exact ⟨dag094 x, dag094_allowed x, dag094_true x, dag094_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row094_exact.2 ha ht

-- 95: XOR, Y_IMPLIES_X; reachable DAG cost 1
def dag095 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag095_allowed (x : α) : (dag095 x).Allowed row095.basis := by
  intro i
  simp [dag095, row095]

theorem dag095_true (x : α) : (dag095 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag095, applyOp, hv] <;> decide

theorem dag095_cost (x : α) : (dag095 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag095]
  decide

theorem row095_dag_exact (x : α) : ExactDagOver α row095.basis 1 := by
  constructor
  · exact ⟨dag095 x, dag095_allowed x, dag095_true x, dag095_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row095_exact.2 ha ht

-- 96: XOR, NOT_X; reachable DAG cost 2
def dag096 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 6 else 12
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag096_allowed (x : α) : (dag096 x).Allowed row096.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag096, row096, h]

theorem dag096_true (x : α) : (dag096 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag096, applyOp, hv] <;> decide

theorem dag096_cost (x : α) : (dag096 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag096]
  decide

theorem row096_dag_exact (x : α) : ExactDagOver α row096.basis 2 := by
  constructor
  · exact ⟨dag096 x, dag096_allowed x, dag096_true x, dag096_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row096_exact.2 ha ht

-- 97: XOR, X_IMPLIES_Y; reachable DAG cost 1
def dag097 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag097_allowed (x : α) : (dag097 x).Allowed row097.basis := by
  intro i
  simp [dag097, row097]

theorem dag097_true (x : α) : (dag097 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag097, applyOp, hv] <;> decide

theorem dag097_cost (x : α) : (dag097 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag097]
  decide

theorem row097_dag_exact (x : α) : ExactDagOver α row097.basis 1 := by
  constructor
  · exact ⟨dag097 x, dag097_allowed x, dag097_true x, dag097_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row097_exact.2 ha ht

-- 98: XOR, NAND; reachable DAG cost 2
def dag098 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 6 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else ((.gate ⟨0, by omega⟩), (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag098_allowed (x : α) : (dag098 x).Allowed row098.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag098, row098, h]

theorem dag098_true (x : α) : (dag098 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag098, applyOp, hv] <;> decide

theorem dag098_cost (x : α) : (dag098 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag098]
  decide

theorem row098_dag_exact (x : α) : ExactDagOver α row098.basis 2 := by
  constructor
  · exact ⟨dag098 x, dag098_allowed x, dag098_true x, dag098_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row098_exact.2 ha ht

-- 99: XOR, TRUE; reachable DAG cost 1
def dag099 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag099_allowed (x : α) : (dag099 x).Allowed row099.basis := by
  intro i
  simp [dag099, row099]

theorem dag099_true (x : α) : (dag099 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag099, applyOp, hv] <;> decide

theorem dag099_cost (x : α) : (dag099 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag099]
  decide

theorem row099_dag_exact (x : α) : ExactDagOver α row099.basis 1 := by
  constructor
  · exact ⟨dag099 x, dag099_allowed x, dag099_true x, dag099_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row099_exact.2 ha ht

-- 100: OR, NOR; reachable DAG cost 2
def dag100 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 8 else 7
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag100_allowed (x : α) : (dag100 x).Allowed row100.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag100, row100, h]

theorem dag100_true (x : α) : (dag100 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag100, applyOp, hv] <;> decide

theorem dag100_cost (x : α) : (dag100 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag100]
  decide

theorem row100_dag_exact (x : α) : ExactDagOver α row100.basis 2 := by
  constructor
  · exact ⟨dag100 x, dag100_allowed x, dag100_true x, dag100_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row100_exact.2 ha ht

-- 101: OR, XNOR; reachable DAG cost 1
def dag101 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag101_allowed (x : α) : (dag101 x).Allowed row101.basis := by
  intro i
  simp [dag101, row101]

theorem dag101_true (x : α) : (dag101 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag101, applyOp, hv] <;> decide

theorem dag101_cost (x : α) : (dag101 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag101]
  decide

theorem row101_dag_exact (x : α) : ExactDagOver α row101.basis 1 := by
  constructor
  · exact ⟨dag101 x, dag101_allowed x, dag101_true x, dag101_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row101_exact.2 ha ht

-- 102: OR, NOT_Y; reachable DAG cost 2
def dag102 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 10 else 7
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag102_allowed (x : α) : (dag102 x).Allowed row102.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag102, row102, h]

theorem dag102_true (x : α) : (dag102 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag102, applyOp, hv] <;> decide

theorem dag102_cost (x : α) : (dag102 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag102]
  decide

theorem row102_dag_exact (x : α) : ExactDagOver α row102.basis 2 := by
  constructor
  · exact ⟨dag102 x, dag102_allowed x, dag102_true x, dag102_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row102_exact.2 ha ht

-- 103: OR, Y_IMPLIES_X; reachable DAG cost 1
def dag103 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag103_allowed (x : α) : (dag103 x).Allowed row103.basis := by
  intro i
  simp [dag103, row103]

theorem dag103_true (x : α) : (dag103 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag103, applyOp, hv] <;> decide

theorem dag103_cost (x : α) : (dag103 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag103]
  decide

theorem row103_dag_exact (x : α) : ExactDagOver α row103.basis 1 := by
  constructor
  · exact ⟨dag103 x, dag103_allowed x, dag103_true x, dag103_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row103_exact.2 ha ht

-- 104: OR, NOT_X; reachable DAG cost 2
def dag104 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 12 else 7
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag104_allowed (x : α) : (dag104 x).Allowed row104.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag104, row104, h]

theorem dag104_true (x : α) : (dag104 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag104, applyOp, hv] <;> decide

theorem dag104_cost (x : α) : (dag104 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag104]
  decide

theorem row104_dag_exact (x : α) : ExactDagOver α row104.basis 2 := by
  constructor
  · exact ⟨dag104 x, dag104_allowed x, dag104_true x, dag104_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row104_exact.2 ha ht

-- 105: OR, X_IMPLIES_Y; reachable DAG cost 1
def dag105 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag105_allowed (x : α) : (dag105 x).Allowed row105.basis := by
  intro i
  simp [dag105, row105]

theorem dag105_true (x : α) : (dag105 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag105, applyOp, hv] <;> decide

theorem dag105_cost (x : α) : (dag105 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag105]
  decide

theorem row105_dag_exact (x : α) : ExactDagOver α row105.basis 1 := by
  constructor
  · exact ⟨dag105 x, dag105_allowed x, dag105_true x, dag105_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row105_exact.2 ha ht

-- 106: OR, NAND; reachable DAG cost 2
def dag106 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 14 else 7
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag106_allowed (x : α) : (dag106 x).Allowed row106.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag106, row106, h]

theorem dag106_true (x : α) : (dag106 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag106, applyOp, hv] <;> decide

theorem dag106_cost (x : α) : (dag106 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag106]
  decide

theorem row106_dag_exact (x : α) : ExactDagOver α row106.basis 2 := by
  constructor
  · exact ⟨dag106 x, dag106_allowed x, dag106_true x, dag106_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row106_exact.2 ha ht

-- 107: OR, TRUE; reachable DAG cost 1
def dag107 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag107_allowed (x : α) : (dag107 x).Allowed row107.basis := by
  intro i
  simp [dag107, row107]

theorem dag107_true (x : α) : (dag107 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag107, applyOp, hv] <;> decide

theorem dag107_cost (x : α) : (dag107 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag107]
  decide

theorem row107_dag_exact (x : α) : ExactDagOver α row107.basis 1 := by
  constructor
  · exact ⟨dag107 x, dag107_allowed x, dag107_true x, dag107_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row107_exact.2 ha ht

-- 108: NOR, XNOR; reachable DAG cost 1
def dag108 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag108_allowed (x : α) : (dag108 x).Allowed row108.basis := by
  intro i
  simp [dag108, row108]

theorem dag108_true (x : α) : (dag108 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag108, applyOp, hv] <;> decide

theorem dag108_cost (x : α) : (dag108 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag108]
  decide

theorem row108_dag_exact (x : α) : ExactDagOver α row108.basis 1 := by
  constructor
  · exact ⟨dag108 x, dag108_allowed x, dag108_true x, dag108_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row108_exact.2 ha ht

-- 109: NOR, NOT_Y; reachable DAG cost 3
def dag109 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 8 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag109_allowed (x : α) : (dag109 x).Allowed row109.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag109, row109, h]

theorem dag109_true (x : α) : (dag109 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag109, applyOp, hv] <;> decide

theorem dag109_cost (x : α) : (dag109 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag109]
  decide

theorem row109_dag_exact (x : α) : ExactDagOver α row109.basis 3 := by
  constructor
  · exact ⟨dag109 x, dag109_allowed x, dag109_true x, dag109_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row109_exact.2 ha ht

-- 110: NOR, Y_IMPLIES_X; reachable DAG cost 1
def dag110 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag110_allowed (x : α) : (dag110 x).Allowed row110.basis := by
  intro i
  simp [dag110, row110]

theorem dag110_true (x : α) : (dag110 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag110, applyOp, hv] <;> decide

theorem dag110_cost (x : α) : (dag110 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag110]
  decide

theorem row110_dag_exact (x : α) : ExactDagOver α row110.basis 1 := by
  constructor
  · exact ⟨dag110 x, dag110_allowed x, dag110_true x, dag110_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row110_exact.2 ha ht

-- 111: NOR, NOT_X; reachable DAG cost 3
def dag111 (x : α) : Dag α where
  allocated := 3
  label i := if i.val = 0 then 8 else if i.val = 1 then 8 else 8
  pins i := if h0 : i.val = 0 then (.input x, .input x) else if h1 : i.val = 1 then (.input x, (.gate ⟨0, by omega⟩)) else ((.gate ⟨1, by omega⟩), (.gate ⟨1, by omega⟩))
  output := .gate ⟨2, by decide⟩

theorem dag111_allowed (x : α) : (dag111 x).Allowed row111.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hb := i.isLt
    change i.val < 3 at hb
    omega
  rcases hi with h | h | h
  all_goals simp [dag111, row111, h]

theorem dag111_true (x : α) : (dag111 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag111, applyOp, hv] <;> decide

theorem dag111_cost (x : α) : (dag111 x).reachableCount = 3 := by
  simp [Dag.reachableCount, Dag.ancestors, dag111]
  decide

theorem row111_dag_exact (x : α) : ExactDagOver α row111.basis 3 := by
  constructor
  · exact ⟨dag111 x, dag111_allowed x, dag111_true x, dag111_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row111_exact.2 ha ht

-- 112: NOR, X_IMPLIES_Y; reachable DAG cost 1
def dag112 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag112_allowed (x : α) : (dag112 x).Allowed row112.basis := by
  intro i
  simp [dag112, row112]

theorem dag112_true (x : α) : (dag112 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag112, applyOp, hv] <;> decide

theorem dag112_cost (x : α) : (dag112 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag112]
  decide

theorem row112_dag_exact (x : α) : ExactDagOver α row112.basis 1 := by
  constructor
  · exact ⟨dag112 x, dag112_allowed x, dag112_true x, dag112_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row112_exact.2 ha ht

-- 113: NOR, NAND; reachable DAG cost 2
def dag113 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 8 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag113_allowed (x : α) : (dag113 x).Allowed row113.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag113, row113, h]

theorem dag113_true (x : α) : (dag113 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag113, applyOp, hv] <;> decide

theorem dag113_cost (x : α) : (dag113 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag113]
  decide

theorem row113_dag_exact (x : α) : ExactDagOver α row113.basis 2 := by
  constructor
  · exact ⟨dag113 x, dag113_allowed x, dag113_true x, dag113_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row113_exact.2 ha ht

-- 114: NOR, TRUE; reachable DAG cost 1
def dag114 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag114_allowed (x : α) : (dag114 x).Allowed row114.basis := by
  intro i
  simp [dag114, row114]

theorem dag114_true (x : α) : (dag114 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag114, applyOp, hv] <;> decide

theorem dag114_cost (x : α) : (dag114 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag114]
  decide

theorem row114_dag_exact (x : α) : ExactDagOver α row114.basis 1 := by
  constructor
  · exact ⟨dag114 x, dag114_allowed x, dag114_true x, dag114_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row114_exact.2 ha ht

-- 115: XNOR, NOT_Y; reachable DAG cost 1
def dag115 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag115_allowed (x : α) : (dag115 x).Allowed row115.basis := by
  intro i
  simp [dag115, row115]

theorem dag115_true (x : α) : (dag115 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag115, applyOp, hv] <;> decide

theorem dag115_cost (x : α) : (dag115 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag115]
  decide

theorem row115_dag_exact (x : α) : ExactDagOver α row115.basis 1 := by
  constructor
  · exact ⟨dag115 x, dag115_allowed x, dag115_true x, dag115_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row115_exact.2 ha ht

-- 116: XNOR, Y_IMPLIES_X; reachable DAG cost 1
def dag116 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag116_allowed (x : α) : (dag116 x).Allowed row116.basis := by
  intro i
  simp [dag116, row116]

theorem dag116_true (x : α) : (dag116 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag116, applyOp, hv] <;> decide

theorem dag116_cost (x : α) : (dag116 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag116]
  decide

theorem row116_dag_exact (x : α) : ExactDagOver α row116.basis 1 := by
  constructor
  · exact ⟨dag116 x, dag116_allowed x, dag116_true x, dag116_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row116_exact.2 ha ht

-- 117: XNOR, NOT_X; reachable DAG cost 1
def dag117 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag117_allowed (x : α) : (dag117 x).Allowed row117.basis := by
  intro i
  simp [dag117, row117]

theorem dag117_true (x : α) : (dag117 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag117, applyOp, hv] <;> decide

theorem dag117_cost (x : α) : (dag117 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag117]
  decide

theorem row117_dag_exact (x : α) : ExactDagOver α row117.basis 1 := by
  constructor
  · exact ⟨dag117 x, dag117_allowed x, dag117_true x, dag117_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row117_exact.2 ha ht

-- 118: XNOR, X_IMPLIES_Y; reachable DAG cost 1
def dag118 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag118_allowed (x : α) : (dag118 x).Allowed row118.basis := by
  intro i
  simp [dag118, row118]

theorem dag118_true (x : α) : (dag118 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag118, applyOp, hv] <;> decide

theorem dag118_cost (x : α) : (dag118 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag118]
  decide

theorem row118_dag_exact (x : α) : ExactDagOver α row118.basis 1 := by
  constructor
  · exact ⟨dag118 x, dag118_allowed x, dag118_true x, dag118_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row118_exact.2 ha ht

-- 119: XNOR, NAND; reachable DAG cost 1
def dag119 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag119_allowed (x : α) : (dag119 x).Allowed row119.basis := by
  intro i
  simp [dag119, row119]

theorem dag119_true (x : α) : (dag119 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag119, applyOp, hv] <;> decide

theorem dag119_cost (x : α) : (dag119 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag119]
  decide

theorem row119_dag_exact (x : α) : ExactDagOver α row119.basis 1 := by
  constructor
  · exact ⟨dag119 x, dag119_allowed x, dag119_true x, dag119_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row119_exact.2 ha ht

-- 120: XNOR, TRUE; reachable DAG cost 1
def dag120 (x : α) : Dag α where
  allocated := 1
  label i := 9
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag120_allowed (x : α) : (dag120 x).Allowed row120.basis := by
  intro i
  simp [dag120, row120]

theorem dag120_true (x : α) : (dag120 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag120, applyOp, hv] <;> decide

theorem dag120_cost (x : α) : (dag120 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag120]
  decide

theorem row120_dag_exact (x : α) : ExactDagOver α row120.basis 1 := by
  constructor
  · exact ⟨dag120 x, dag120_allowed x, dag120_true x, dag120_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row120_exact.2 ha ht

-- 121: NOT_Y, Y_IMPLIES_X; reachable DAG cost 1
def dag121 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag121_allowed (x : α) : (dag121 x).Allowed row121.basis := by
  intro i
  simp [dag121, row121]

theorem dag121_true (x : α) : (dag121 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag121, applyOp, hv] <;> decide

theorem dag121_cost (x : α) : (dag121 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag121]
  decide

theorem row121_dag_exact (x : α) : ExactDagOver α row121.basis 1 := by
  constructor
  · exact ⟨dag121 x, dag121_allowed x, dag121_true x, dag121_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row121_exact.2 ha ht

theorem row122_dag_blocked (c : Dag α) (ha : c.Allowed row122.basis) :
    ¬c.IsTrue := c.blocked_of_formula row122_blocked ha

-- 123: NOT_Y, X_IMPLIES_Y; reachable DAG cost 1
def dag123 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag123_allowed (x : α) : (dag123 x).Allowed row123.basis := by
  intro i
  simp [dag123, row123]

theorem dag123_true (x : α) : (dag123 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag123, applyOp, hv] <;> decide

theorem dag123_cost (x : α) : (dag123 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag123]
  decide

theorem row123_dag_exact (x : α) : ExactDagOver α row123.basis 1 := by
  constructor
  · exact ⟨dag123 x, dag123_allowed x, dag123_true x, dag123_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row123_exact.2 ha ht

-- 124: NOT_Y, NAND; reachable DAG cost 2
def dag124 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 10 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag124_allowed (x : α) : (dag124 x).Allowed row124.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag124, row124, h]

theorem dag124_true (x : α) : (dag124 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag124, applyOp, hv] <;> decide

theorem dag124_cost (x : α) : (dag124 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag124]
  decide

theorem row124_dag_exact (x : α) : ExactDagOver α row124.basis 2 := by
  constructor
  · exact ⟨dag124 x, dag124_allowed x, dag124_true x, dag124_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row124_exact.2 ha ht

-- 125: NOT_Y, TRUE; reachable DAG cost 1
def dag125 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag125_allowed (x : α) : (dag125 x).Allowed row125.basis := by
  intro i
  simp [dag125, row125]

theorem dag125_true (x : α) : (dag125 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag125, applyOp, hv] <;> decide

theorem dag125_cost (x : α) : (dag125 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag125]
  decide

theorem row125_dag_exact (x : α) : ExactDagOver α row125.basis 1 := by
  constructor
  · exact ⟨dag125 x, dag125_allowed x, dag125_true x, dag125_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row125_exact.2 ha ht

-- 126: Y_IMPLIES_X, NOT_X; reachable DAG cost 1
def dag126 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag126_allowed (x : α) : (dag126 x).Allowed row126.basis := by
  intro i
  simp [dag126, row126]

theorem dag126_true (x : α) : (dag126 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag126, applyOp, hv] <;> decide

theorem dag126_cost (x : α) : (dag126 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag126]
  decide

theorem row126_dag_exact (x : α) : ExactDagOver α row126.basis 1 := by
  constructor
  · exact ⟨dag126 x, dag126_allowed x, dag126_true x, dag126_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row126_exact.2 ha ht

-- 127: Y_IMPLIES_X, X_IMPLIES_Y; reachable DAG cost 1
def dag127 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag127_allowed (x : α) : (dag127 x).Allowed row127.basis := by
  intro i
  simp [dag127, row127]

theorem dag127_true (x : α) : (dag127 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag127, applyOp, hv] <;> decide

theorem dag127_cost (x : α) : (dag127 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag127]
  decide

theorem row127_dag_exact (x : α) : ExactDagOver α row127.basis 1 := by
  constructor
  · exact ⟨dag127 x, dag127_allowed x, dag127_true x, dag127_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row127_exact.2 ha ht

-- 128: Y_IMPLIES_X, NAND; reachable DAG cost 1
def dag128 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag128_allowed (x : α) : (dag128 x).Allowed row128.basis := by
  intro i
  simp [dag128, row128]

theorem dag128_true (x : α) : (dag128 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag128, applyOp, hv] <;> decide

theorem dag128_cost (x : α) : (dag128 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag128]
  decide

theorem row128_dag_exact (x : α) : ExactDagOver α row128.basis 1 := by
  constructor
  · exact ⟨dag128 x, dag128_allowed x, dag128_true x, dag128_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row128_exact.2 ha ht

-- 129: Y_IMPLIES_X, TRUE; reachable DAG cost 1
def dag129 (x : α) : Dag α where
  allocated := 1
  label i := 11
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag129_allowed (x : α) : (dag129 x).Allowed row129.basis := by
  intro i
  simp [dag129, row129]

theorem dag129_true (x : α) : (dag129 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag129, applyOp, hv] <;> decide

theorem dag129_cost (x : α) : (dag129 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag129]
  decide

theorem row129_dag_exact (x : α) : ExactDagOver α row129.basis 1 := by
  constructor
  · exact ⟨dag129 x, dag129_allowed x, dag129_true x, dag129_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row129_exact.2 ha ht

-- 130: NOT_X, X_IMPLIES_Y; reachable DAG cost 1
def dag130 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag130_allowed (x : α) : (dag130 x).Allowed row130.basis := by
  intro i
  simp [dag130, row130]

theorem dag130_true (x : α) : (dag130 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag130, applyOp, hv] <;> decide

theorem dag130_cost (x : α) : (dag130 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag130]
  decide

theorem row130_dag_exact (x : α) : ExactDagOver α row130.basis 1 := by
  constructor
  · exact ⟨dag130 x, dag130_allowed x, dag130_true x, dag130_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row130_exact.2 ha ht

-- 131: NOT_X, NAND; reachable DAG cost 2
def dag131 (x : α) : Dag α where
  allocated := 2
  label i := if i.val = 0 then 12 else 14
  pins i := if h0 : i.val = 0 then (.input x, .input x) else (.input x, (.gate ⟨0, by omega⟩))
  output := .gate ⟨1, by decide⟩

theorem dag131_allowed (x : α) : (dag131 x).Allowed row131.basis := by
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hb := i.isLt
    change i.val < 2 at hb
    omega
  rcases hi with h | h
  all_goals simp [dag131, row131, h]

theorem dag131_true (x : α) : (dag131 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag131, applyOp, hv] <;> decide

theorem dag131_cost (x : α) : (dag131 x).reachableCount = 2 := by
  simp [Dag.reachableCount, Dag.ancestors, dag131]
  decide

theorem row131_dag_exact (x : α) : ExactDagOver α row131.basis 2 := by
  constructor
  · exact ⟨dag131 x, dag131_allowed x, dag131_true x, dag131_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row131_exact.2 ha ht

-- 132: NOT_X, TRUE; reachable DAG cost 1
def dag132 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag132_allowed (x : α) : (dag132 x).Allowed row132.basis := by
  intro i
  simp [dag132, row132]

theorem dag132_true (x : α) : (dag132 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag132, applyOp, hv] <;> decide

theorem dag132_cost (x : α) : (dag132 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag132]
  decide

theorem row132_dag_exact (x : α) : ExactDagOver α row132.basis 1 := by
  constructor
  · exact ⟨dag132 x, dag132_allowed x, dag132_true x, dag132_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row132_exact.2 ha ht

-- 133: X_IMPLIES_Y, NAND; reachable DAG cost 1
def dag133 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag133_allowed (x : α) : (dag133 x).Allowed row133.basis := by
  intro i
  simp [dag133, row133]

theorem dag133_true (x : α) : (dag133 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag133, applyOp, hv] <;> decide

theorem dag133_cost (x : α) : (dag133 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag133]
  decide

theorem row133_dag_exact (x : α) : ExactDagOver α row133.basis 1 := by
  constructor
  · exact ⟨dag133 x, dag133_allowed x, dag133_true x, dag133_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row133_exact.2 ha ht

-- 134: X_IMPLIES_Y, TRUE; reachable DAG cost 1
def dag134 (x : α) : Dag α where
  allocated := 1
  label i := 13
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag134_allowed (x : α) : (dag134 x).Allowed row134.basis := by
  intro i
  simp [dag134, row134]

theorem dag134_true (x : α) : (dag134 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag134, applyOp, hv] <;> decide

theorem dag134_cost (x : α) : (dag134 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag134]
  decide

theorem row134_dag_exact (x : α) : ExactDagOver α row134.basis 1 := by
  constructor
  · exact ⟨dag134 x, dag134_allowed x, dag134_true x, dag134_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row134_exact.2 ha ht

-- 135: NAND, TRUE; reachable DAG cost 1
def dag135 (x : α) : Dag α where
  allocated := 1
  label i := 15
  pins i := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

theorem dag135_allowed (x : α) : (dag135 x).Allowed row135.basis := by
  intro i
  simp [dag135, row135]

theorem dag135_true (x : α) : (dag135 x).IsTrue := by
  intro v
  cases hv : v x <;>
    simp [Dag.eval, Dag.formula, Dag.unfold, Formula.eval, dag135, applyOp, hv] <;> decide

theorem dag135_cost (x : α) : (dag135 x).reachableCount = 1 := by
  simp [Dag.reachableCount, Dag.ancestors, dag135]
  decide

theorem row135_dag_exact (x : α) : ExactDagOver α row135.basis 1 := by
  constructor
  · exact ⟨dag135 x, dag135_allowed x, dag135_true x, dag135_cost x⟩
  · intro c ha ht
    exact c.lower_of_depth x row135_exact.2 ha ht


/-- A single row records either exact reachable cost or an unbounded obstruction. -/
def RowDagResult (α : Type) (r : Row) : Prop :=
  if r.generates then ExactDagOver α r.basis r.depthCost
  else ∀ c : Dag α, c.Allowed r.basis → ¬c.IsTrue

def AllDagResults (α : Type) : List Row → Prop
  | [] => True
  | r :: rest => RowDagResult α r ∧ AllDagResults α rest

theorem all_dag_results (x : α) : AllDagResults α rows := by
  exact ⟨row000_dag_blocked, ⟨row001_dag_blocked, ⟨row002_dag_blocked, ⟨row003_dag_blocked, ⟨row004_dag_blocked, ⟨row005_dag_blocked, ⟨row006_dag_blocked, ⟨row007_dag_blocked, ⟨row008_dag_exact x, ⟨row009_dag_exact x, ⟨row010_dag_blocked, ⟨row011_dag_exact x, ⟨row012_dag_blocked, ⟨row013_dag_exact x, ⟨row014_dag_exact x, ⟨row015_dag_exact x, ⟨row016_dag_blocked, ⟨row017_dag_blocked, ⟨row018_dag_blocked, ⟨row019_dag_blocked, ⟨row020_dag_blocked, ⟨row021_dag_blocked, ⟨row022_dag_blocked, ⟨row023_dag_exact x, ⟨row024_dag_exact x, ⟨row025_dag_exact x, ⟨row026_dag_exact x, ⟨row027_dag_exact x, ⟨row028_dag_exact x, ⟨row029_dag_exact x, ⟨row030_dag_exact x, ⟨row031_dag_blocked, ⟨row032_dag_blocked, ⟨row033_dag_blocked, ⟨row034_dag_blocked, ⟨row035_dag_blocked, ⟨row036_dag_blocked, ⟨row037_dag_exact x, ⟨row038_dag_exact x, ⟨row039_dag_exact x, ⟨row040_dag_exact x, ⟨row041_dag_exact x, ⟨row042_dag_exact x, ⟨row043_dag_exact x, ⟨row044_dag_exact x, ⟨row045_dag_blocked, ⟨row046_dag_blocked, ⟨row047_dag_blocked, ⟨row048_dag_blocked, ⟨row049_dag_blocked, ⟨row050_dag_exact x, ⟨row051_dag_exact x, ⟨row052_dag_exact x, ⟨row053_dag_exact x, ⟨row054_dag_exact x, ⟨row055_dag_exact x, ⟨row056_dag_exact x, ⟨row057_dag_exact x, ⟨row058_dag_blocked, ⟨row059_dag_blocked, ⟨row060_dag_blocked, ⟨row061_dag_blocked, ⟨row062_dag_exact x, ⟨row063_dag_exact x, ⟨row064_dag_blocked, ⟨row065_dag_exact x, ⟨row066_dag_blocked, ⟨row067_dag_exact x, ⟨row068_dag_exact x, ⟨row069_dag_exact x, ⟨row070_dag_blocked, ⟨row071_dag_blocked, ⟨row072_dag_blocked, ⟨row073_dag_exact x, ⟨row074_dag_exact x, ⟨row075_dag_exact x, ⟨row076_dag_exact x, ⟨row077_dag_exact x, ⟨row078_dag_exact x, ⟨row079_dag_exact x, ⟨row080_dag_exact x, ⟨row081_dag_blocked, ⟨row082_dag_blocked, ⟨row083_dag_exact x, ⟨row084_dag_exact x, ⟨row085_dag_blocked, ⟨row086_dag_exact x, ⟨row087_dag_blocked, ⟨row088_dag_exact x, ⟨row089_dag_exact x, ⟨row090_dag_exact x, ⟨row091_dag_blocked, ⟨row092_dag_exact x, ⟨row093_dag_exact x, ⟨row094_dag_exact x, ⟨row095_dag_exact x, ⟨row096_dag_exact x, ⟨row097_dag_exact x, ⟨row098_dag_exact x, ⟨row099_dag_exact x, ⟨row100_dag_exact x, ⟨row101_dag_exact x, ⟨row102_dag_exact x, ⟨row103_dag_exact x, ⟨row104_dag_exact x, ⟨row105_dag_exact x, ⟨row106_dag_exact x, ⟨row107_dag_exact x, ⟨row108_dag_exact x, ⟨row109_dag_exact x, ⟨row110_dag_exact x, ⟨row111_dag_exact x, ⟨row112_dag_exact x, ⟨row113_dag_exact x, ⟨row114_dag_exact x, ⟨row115_dag_exact x, ⟨row116_dag_exact x, ⟨row117_dag_exact x, ⟨row118_dag_exact x, ⟨row119_dag_exact x, ⟨row120_dag_exact x, ⟨row121_dag_exact x, ⟨row122_dag_blocked, ⟨row123_dag_exact x, ⟨row124_dag_exact x, ⟨row125_dag_exact x, ⟨row126_dag_exact x, ⟨row127_dag_exact x, ⟨row128_dag_exact x, ⟨row129_dag_exact x, ⟨row130_dag_exact x, ⟨row131_dag_exact x, ⟨row132_dag_exact x, ⟨row133_dag_exact x, ⟨row134_dag_exact x, ⟨row135_dag_exact x, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩


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

end
end FIG22.Basis
