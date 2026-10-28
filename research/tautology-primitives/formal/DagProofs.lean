import Std

/-!
Singleton TRUE-generation costs for finite shared Boolean circuits.

Gate references carry a strict topological bound.  The output may name any
source or allocated gate.  Cost is the number of distinct ancestors of that
output, so allocated gates outside its ancestry do not contribute.
-/
namespace FIG22.DAG

inductive Op where
  | nor | nand | xnor | yImpliesX | xImpliesY | binaryTrue
  deriving DecidableEq, Repr

def Op.apply : Op → Bool → Bool → Bool
  | .nor, a, b => !(a || b)
  | .nand, a, b => !(a && b)
  | .xnor, a, b => a == b
  | .yImpliesX, a, b => !b || a
  | .xImpliesY, a, b => !a || b
  | .binaryTrue, _, _ => true

inductive Ref (n k : Nat) where
  | input : Fin n → Ref n k
  | gate : Fin k → Ref n k
  deriving DecidableEq, Repr

structure Circuit (n : Nat) where
  allocated : Nat
  op : Op
  pins : (i : Fin allocated) → Ref n i.val × Ref n i.val
  output : Ref n allocated

def Circuit.value (c : Circuit n) (ρ : Fin n → Bool)
    {k : Nat} (hk : k ≤ c.allocated) : Ref n k → Bool
  | .input i => ρ i
  | .gate i =>
      let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
      c.op.apply (c.value ρ h (c.pins j).1) (c.value ρ h (c.pins j).2)
termination_by k

def Circuit.ancestors (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) : Ref n k → List Nat
  | .input _ => []
  | .gate i =>
      let j : Fin c.allocated := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      let h : i.val ≤ c.allocated := Nat.le_of_lt j.isLt
      (i.val :: c.ancestors h (c.pins j).1 ++
        c.ancestors h (c.pins j).2).eraseDups
termination_by k

def Circuit.reachableCount (c : Circuit n) : Nat :=
  (c.ancestors (Nat.le_refl _) c.output).length

def Circuit.eval (c : Circuit n) (ρ : Fin n → Bool) : Bool :=
  c.value ρ (Nat.le_refl _) c.output

def Circuit.IsTrue (c : Circuit n) : Prop := ∀ ρ, c.eval ρ = true

theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_eraseDups]
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun b : Nat => !b == a) xs
  simp only [List.length_cons]
  omega

/-- Every charged gate index occurs once in the ancestry list. -/
theorem Circuit.ancestors_nodup (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (r : Ref n k) :
    (c.ancestors hk r).Nodup := by
  cases r with
  | input i => simp [Circuit.ancestors]
  | gate i => simpa only [Circuit.ancestors] using eraseDups_nodup _

theorem value_input (c : Circuit n) (ρ : Fin n → Bool)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin n) :
    c.value ρ hk (.input i) = ρ i := by
  simp [Circuit.value]

theorem value_gate (c : Circuit n) (ρ : Fin n → Bool)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin k) :
    c.value ρ hk (.gate i) =
      c.op.apply
        (c.value ρ (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
          (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).1)
        (c.value ρ (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
          (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).2) := by
  simp [Circuit.value]

theorem ancestors_gate (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin k) :
    c.ancestors hk (.gate i) =
      (i.val :: c.ancestors (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
          (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).1 ++
        c.ancestors (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
          (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).2).eraseDups := by
  simp [Circuit.ancestors]

theorem own_mem_ancestors (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin k) :
    i.val ∈ c.ancestors hk (.gate i) := by
  simp [ancestors_gate]

theorem left_ancestors_subset (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin k) :
    c.ancestors (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
      (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).1 ⊆
      c.ancestors hk (.gate i) := by
  intro a ha
  simp only [ancestors_gate, List.mem_eraseDups, List.mem_cons, List.mem_append]
  exact Or.inl (Or.inr ha)

theorem right_ancestors_subset (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (i : Fin k) :
    c.ancestors (Nat.le_of_lt (Nat.lt_of_lt_of_le i.isLt hk))
      (c.pins ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).2 ⊆
      c.ancestors hk (.gate i) := by
  intro a ha
  simp only [ancestors_gate, List.mem_eraseDups, List.mem_cons, List.mem_append]
  exact Or.inr ha

theorem two_le_length_of_distinct_mem {a b : Nat} {xs : List Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) : 2 ≤ xs.length := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys => simp

theorem three_le_length_of_distinct_mem {a b d : Nat} {xs : List Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hd : d ∈ xs)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) : 3 ≤ xs.length := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys =>
      cases ys with
      | nil => simp_all only [List.mem_cons, List.not_mem_nil, or_false]
               omega
      | cons z zs => simp

theorem positive_lower_bound (c : Circuit n) (h : c.IsTrue) :
    1 ≤ c.reachableCount := by
  cases ho : c.output with
  | input i =>
    have hfalse := h (fun _ => false)
    simp [Circuit.eval, ho, Circuit.value] at hfalse
  | gate i =>
    have hm := own_mem_ancestors c (Nat.le_refl _) i
    have hn : (c.ancestors (Nat.le_refl _) (.gate i)).length > 0 :=
      List.length_pos_of_mem hm
    simpa [Circuit.reachableCount, ho] using (Nat.succ_le_of_lt hn)

theorem true_at_false_is_gate (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (r : Ref n k)
    (h : c.value (fun _ => false) hk r = true) :
    ∃ i : Fin k, r = .gate i := by
  cases r with
  | input i => simp [Circuit.value] at h
  | gate i => exact ⟨i, rfl⟩

theorem false_at_true_is_gate (c : Circuit n)
    {k : Nat} (hk : k ≤ c.allocated) (r : Ref n k)
    (h : c.value (fun _ => true) hk r = false) :
    ∃ i : Fin k, r = .gate i := by
  cases r with
  | input i => simp [Circuit.value] at h
  | gate i => exact ⟨i, rfl⟩

theorem nor_true_inputs (a b : Bool) (h : Op.nor.apply a b = true) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all [Op.apply]

theorem nor_false_input (a b : Bool) (h : Op.nor.apply a b = false) :
    a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [Op.apply]

theorem nand_true_input (a b : Bool) (h : Op.nand.apply a b = true) :
    a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all [Op.apply]

theorem nor_lower_bound (c : Circuit n) (hop : c.op = .nor) (h : c.IsTrue) :
    3 ≤ c.reachableCount := by
  cases ho : c.output with
  | input i =>
    have hfalse := h (fun _ => false)
    simp [Circuit.eval, ho, Circuit.value] at hfalse
  | gate i =>
    let hi := Nat.le_of_lt i.isLt
    have h0 := h (fun _ => false)
    have h1 := h (fun _ => true)
    simp only [Circuit.eval, ho, value_gate, hop] at h0 h1
    have hl0 := (nor_true_inputs _ _ h0).1
    have hl1 := (nor_true_inputs _ _ h1).1
    obtain ⟨j, hj⟩ := false_at_true_is_gate c hi (c.pins i).1 hl1
    have hmI : i.val ∈ c.ancestors (Nat.le_refl _) (.gate i) :=
      own_mem_ancestors c _ i
    have hmJlocal : j.val ∈ c.ancestors hi (c.pins i).1 := by
      rw [hj]
      exact own_mem_ancestors c _ j
    have hmJ := left_ancestors_subset c (Nat.le_refl _) i hmJlocal
    rw [hj, value_gate, hop] at hl0
    rcases nor_false_input _ _ hl0 with hleft | hright
    · obtain ⟨q, hq⟩ := true_at_false_is_gate c _ _ hleft
      have hmQlocal : q.val ∈ c.ancestors
          (Nat.le_of_lt (Nat.lt_of_lt_of_le j.isLt hi))
          (c.pins ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩).1 := by
        rw [hq]
        exact own_mem_ancestors c _ q
      have hmQj := left_ancestors_subset c hi j hmQlocal
      rw [← hj] at hmQj
      have hmQ := left_ancestors_subset c (Nat.le_refl _) i hmQj
      have hb := three_le_length_of_distinct_mem hmI hmJ hmQ
        (by have := j.isLt; omega) (by have := j.isLt; have := q.isLt; omega)
        (by have := q.isLt; omega)
      simpa [Circuit.reachableCount, ho] using hb
    · obtain ⟨q, hq⟩ := true_at_false_is_gate c _ _ hright
      have hmQlocal : q.val ∈ c.ancestors
          (Nat.le_of_lt (Nat.lt_of_lt_of_le j.isLt hi))
          (c.pins ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩).2 := by
        rw [hq]
        exact own_mem_ancestors c _ q
      have hmQj := right_ancestors_subset c hi j hmQlocal
      rw [← hj] at hmQj
      have hmQ := left_ancestors_subset c (Nat.le_refl _) i hmQj
      have hb := three_le_length_of_distinct_mem hmI hmJ hmQ
        (by have := j.isLt; omega) (by have := j.isLt; have := q.isLt; omega)
        (by have := q.isLt; omega)
      simpa [Circuit.reachableCount, ho] using hb

theorem nand_lower_bound (c : Circuit n) (hop : c.op = .nand) (h : c.IsTrue) :
    2 ≤ c.reachableCount := by
  cases ho : c.output with
  | input i =>
    have hfalse := h (fun _ => false)
    simp [Circuit.eval, ho, Circuit.value] at hfalse
  | gate i =>
    let hi := Nat.le_of_lt i.isLt
    have h1 := h (fun _ => true)
    simp only [Circuit.eval, ho, value_gate, hop] at h1
    have hmI : i.val ∈ c.ancestors (Nat.le_refl _) (.gate i) :=
      own_mem_ancestors c _ i
    rcases nand_true_input _ _ h1 with hleft | hright
    · obtain ⟨j, hj⟩ := false_at_true_is_gate c hi _ hleft
      have hmJlocal : j.val ∈ c.ancestors hi (c.pins i).1 := by
        rw [hj]
        exact own_mem_ancestors c _ j
      have hmJ := left_ancestors_subset c (Nat.le_refl _) i hmJlocal
      have hb := two_le_length_of_distinct_mem hmI hmJ (by have := j.isLt; omega)
      simpa [Circuit.reachableCount, ho] using hb
    · obtain ⟨j, hj⟩ := false_at_true_is_gate c hi _ hright
      have hmJlocal : j.val ∈ c.ancestors hi (c.pins i).2 := by
        rw [hj]
        exact own_mem_ancestors c _ j
      have hmJ := right_ancestors_subset c (Nat.le_refl _) i hmJlocal
      have hb := two_le_length_of_distinct_mem hmI hmJ (by have := j.isLt; omega)
      simpa [Circuit.reachableCount, ho] using hb

def oneWitness (op : Op) (x : Fin n) : Circuit n where
  allocated := 1
  op := op
  pins _ := (.input x, .input x)
  output := .gate ⟨0, by decide⟩

def nandWitness (x : Fin n) : Circuit n where
  allocated := 2
  op := .nand
  pins i := if h0 : i.val = 0 then (.input x, .input x)
    else (.input x, .gate ⟨0, by omega⟩)
  output := .gate ⟨1, by decide⟩

def norWitness (x : Fin n) : Circuit n where
  allocated := 3
  op := .nor
  pins i := if h0 : i.val = 0 then (.input x, .input x)
    else if h1 : i.val = 1 then (.input x, .gate ⟨0, by omega⟩)
    else (.gate ⟨1, by omega⟩, .gate ⟨1, by omega⟩)
  output := .gate ⟨2, by decide⟩

theorem oneWitness_cost (op : Op) (x : Fin n) :
    (oneWitness op x).reachableCount = 1 := by
  simp [Circuit.reachableCount, Circuit.ancestors, oneWitness]
  decide

theorem nandWitness_cost (x : Fin n) :
    (nandWitness x).reachableCount = 2 := by
  simp [Circuit.reachableCount, Circuit.ancestors, nandWitness]
  decide

theorem norWitness_cost (x : Fin n) :
    (norWitness x).reachableCount = 3 := by
  simp [Circuit.reachableCount, Circuit.ancestors, norWitness]
  decide

theorem nandWitness_true (x : Fin n) : (nandWitness x).IsTrue := by
  intro ρ
  cases h : ρ x <;> simp [Circuit.eval, Circuit.value, nandWitness, Op.apply, h]

theorem norWitness_true (x : Fin n) : (norWitness x).IsTrue := by
  intro ρ
  cases h : ρ x <;> simp [Circuit.eval, Circuit.value, norWitness, Op.apply, h]

theorem oneWitness_true (op : Op) (x : Fin n)
    (hop : op = .xnor ∨ op = .yImpliesX ∨ op = .xImpliesY ∨ op = .binaryTrue) :
    (oneWitness op x).IsTrue := by
  intro ρ
  rcases hop with rfl | rfl | rfl | rfl <;>
    cases h : ρ x <;> simp [Circuit.eval, Circuit.value, oneWitness, Op.apply, h]

def minimumCost : Op → Nat
  | .nor => 3
  | .nand => 2
  | _ => 1

/-- Exact minimum among all circuits with the stated singleton operation. -/
def HasMinimum (n : Nat) (op : Op) (k : Nat) : Prop :=
  (∀ c : Circuit n, c.op = op → c.IsTrue → k ≤ c.reachableCount) ∧
  ∃ c : Circuit n, c.op = op ∧ c.IsTrue ∧ c.reachableCount = k

theorem singleton_minimum (op : Op) (x : Fin n) : HasMinimum n op (minimumCost op) := by
  constructor
  · intro c hop ht
    cases op with
    | nor => exact nor_lower_bound c hop ht
    | nand => exact nand_lower_bound c hop ht
    | xnor | yImpliesX | xImpliesY | binaryTrue => exact positive_lower_bound c ht
  · cases op with
    | nor => exact ⟨norWitness x, rfl, norWitness_true x, norWitness_cost x⟩
    | nand => exact ⟨nandWitness x, rfl, nandWitness_true x, nandWitness_cost x⟩
    | xnor => exact ⟨oneWitness .xnor x, rfl,
        oneWitness_true .xnor x (Or.inl rfl), oneWitness_cost .xnor x⟩
    | yImpliesX => exact ⟨oneWitness .yImpliesX x, rfl,
        oneWitness_true .yImpliesX x (Or.inr (Or.inl rfl)), oneWitness_cost .yImpliesX x⟩
    | xImpliesY => exact ⟨oneWitness .xImpliesY x, rfl,
        oneWitness_true .xImpliesY x (Or.inr (Or.inr (Or.inl rfl))),
        oneWitness_cost .xImpliesY x⟩
    | binaryTrue => exact ⟨oneWitness .binaryTrue x, rfl,
        oneWitness_true .binaryTrue x (Or.inr (Or.inr (Or.inr rfl))),
        oneWitness_cost .binaryTrue x⟩

/-- Change the interpretation of input names without changing any gate index. -/
def Ref.mapInputs (σ : Fin n → Fin q) : Ref n k → Ref q k
  | .input i => .input (σ i)
  | .gate i => .gate i

abbrev Circuit.renameInputs (c : Circuit n) (σ : Fin n → Fin q) : Circuit q where
  allocated := c.allocated
  op := c.op
  pins i := ((c.pins i).1.mapInputs σ, (c.pins i).2.mapInputs σ)
  output := c.output.mapInputs σ

theorem Circuit.value_renameInputs (c : Circuit n) (σ : Fin n → Fin q)
    (ρ : Fin q → Bool) {k : Nat} (hk : k ≤ c.allocated) (r : Ref n k) :
    (c.renameInputs σ).value ρ hk (r.mapInputs σ) =
      c.value (fun i => ρ (σ i)) hk r := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases r with
    | input i =>
      change (c.renameInputs σ).value ρ hk (.input (σ i)) =
        c.value (fun i => ρ (σ i)) hk (.input i)
      rw [value_input, value_input]
    | gate i =>
      change (c.renameInputs σ).value ρ hk (.gate i) =
        c.value (fun i => ρ (σ i)) hk (.gate i)
      rw [value_gate, value_gate]
      rw [ih i.val i.isLt, ih i.val i.isLt]

theorem Circuit.ancestors_renameInputs (c : Circuit n) (σ : Fin n → Fin q)
    {k : Nat} (hk : k ≤ c.allocated) (r : Ref n k) :
    (c.renameInputs σ).ancestors hk (r.mapInputs σ) = c.ancestors hk r := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases r with
    | input i =>
      change (c.renameInputs σ).ancestors hk (.input (σ i)) =
        c.ancestors hk (.input i)
      rw [Circuit.ancestors, Circuit.ancestors]
    | gate i =>
      change (c.renameInputs σ).ancestors hk (.gate i) =
        c.ancestors hk (.gate i)
      rw [ancestors_gate, ancestors_gate]
      rw [ih i.val i.isLt, ih i.val i.isLt]

theorem Circuit.reachableCount_renameInputs (c : Circuit n) (σ : Fin n → Fin q) :
    (c.renameInputs σ).reachableCount = c.reachableCount := by
  simp only [Circuit.reachableCount, Circuit.renameInputs]
  exact congrArg List.length (c.ancestors_renameInputs σ _ c.output)

theorem Circuit.true_renameInputs (c : Circuit n) (σ : Fin n → Fin q)
    (h : c.IsTrue) : (c.renameInputs σ).IsTrue := by
  intro ρ
  have heq := c.value_renameInputs σ ρ (Nat.le_refl _) c.output
  simpa only [Circuit.eval, Circuit.renameInputs] using heq.trans (h _)

/-- Diagonal substitution is semantic: original input identities are not equated. -/
def Circuit.diagonal (c : Circuit n) : Circuit 1 :=
  c.renameInputs (fun _ => ⟨0, by decide⟩)

theorem Circuit.diagonal_preserves_cost (c : Circuit n) :
    c.diagonal.reachableCount = c.reachableCount :=
  c.reachableCount_renameInputs _

theorem Circuit.diagonal_preserves_true (c : Circuit n) (h : c.IsTrue) :
    c.diagonal.IsTrue := c.true_renameInputs _ h

theorem Circuit.diagonal_preserves_allocated (c : Circuit n) :
    c.diagonal.allocated = c.allocated := rfl

theorem Circuit.diagonal_preserves_operator (c : Circuit n) :
    c.diagonal.op = c.op := rfl

theorem Circuit.renameInputs_gate_pins (c : Circuit n) (σ : Fin n → Fin q)
    (i : Fin c.allocated) :
    (c.renameInputs σ).pins i =
      ((c.pins i).1.mapInputs σ, (c.pins i).2.mapInputs σ) := rfl

end FIG22.DAG
