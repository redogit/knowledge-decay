import Std

/-!
Universal singleton formula-size and depth minima for finite Boolean terms.

Terms are full ordered binary trees. A variable costs zero gates; each
application costs one gate, even when its operation ignores a pin. Repeated
variables and repeated subterms are allowed, and every subterm occurrence is
charged separately. The proofs use two diagonal valuations as a lower-bound
invariant and therefore quantify over trees of arbitrary finite size.
-/

namespace FIG22.Tree

inductive Op where
  | nor | nand | xnor | implies | revImplies | top
  deriving DecidableEq, Repr

def apply : Op → Bool → Bool → Bool
  | .nor, a, b => !(a || b)
  | .nand, a, b => !(a && b)
  | .xnor, a, b => a == b
  | .implies, a, b => !a || b
  | .revImplies, a, b => !b || a
  | .top, _, _ => true

inductive Term (op : Op) (n : Nat) where
  | var : Fin n → Term op n
  | app : Term op n → Term op n → Term op n
  deriving Repr

def eval {op : Op} {n : Nat} (v : Fin n → Bool) : Term op n → Bool
  | .var i => v i
  | .app l r => apply op (eval v l) (eval v r)

def size {op : Op} {n : Nat} : Term op n → Nat
  | .var _ => 0
  | .app l r => 1 + size l + size r

def depth {op : Op} {n : Nat} : Term op n → Nat
  | .var _ => 0
  | .app l r => 1 + max (depth l) (depth r)

def leaves {op : Op} {n : Nat} : Term op n → Nat
  | .var _ => 1
  | .app l r => leaves l + leaves r

theorem leaves_eq_size_add_one {op : Op} {n : Nat} (t : Term op n) :
    leaves t = size t + 1 := by
  induction t with
  | var i => rfl
  | app l r ihl ihr => simp only [leaves, size]; omega

def Tautology {op : Op} {n : Nat} (t : Term op n) : Prop :=
  ∀ v : Fin n → Bool, eval v t = true

/-- Substitute one variable for every input, retaining every tree occurrence. -/
def identify {op : Op} {n : Nat} : Term op n → Term op 1
  | .var _ => .var ⟨0, by decide⟩
  | .app l r => .app (identify l) (identify r)

theorem identify_eval {op : Op} {n : Nat} (t : Term op n)
    (v : Fin 1 → Bool) :
    eval v (identify t) = eval (fun _ => v ⟨0, by decide⟩) t := by
  induction t with
  | var i => rfl
  | app l r ihl ihr => simp only [identify, eval, ihl, ihr]

theorem identify_size {op : Op} {n : Nat} (t : Term op n) :
    size (identify t) = size t := by
  induction t with
  | var i => rfl
  | app l r ihl ihr => simp only [identify, size, ihl, ihr]

theorem identify_depth {op : Op} {n : Nat} (t : Term op n) :
    depth (identify t) = depth t := by
  induction t with
  | var i => rfl
  | app l r ihl ihr => simp only [identify, depth, ihl, ihr]

theorem identify_tautology {op : Op} {n : Nat} (t : Term op n)
    (h : Tautology t) : Tautology (identify t) := by
  intro v
  rw [identify_eval]
  exact h _

def formulaCost : Op → Nat
  | .nor => 5
  | .nand => 2
  | _ => 1

def depthCost : Op → Nat
  | .nor => 3
  | .nand => 2
  | _ => 1

/-- Potential of the unary function described by its outputs at 0 and 1. -/
def sizePotential : Op → Bool → Bool → Nat
  | .nor, false, false => 2
  | .nor, false, true => 0
  | .nor, true, false => 1
  | .nor, true, true => 5
  | .nand, false, false => 1
  | .nand, false, true => 0
  | .nand, true, false => 1
  | .nand, true, true => 2
  | _, true, true => 1
  | _, _, _ => 0

def depthPotential : Op → Bool → Bool → Nat
  | .nor, false, false => 2
  | .nor, false, true => 0
  | .nor, true, false => 1
  | .nor, true, true => 3
  | .nand, false, false => 1
  | .nand, false, true => 0
  | .nand, true, false => 1
  | .nand, true, true => 2
  | _, true, true => 1
  | _, _, _ => 0

/-- The finite check is local to one gate; the later induction is unbounded. -/
theorem sizePotential_apply (op : Op) (a₀ a₁ b₀ b₁ : Bool) :
    sizePotential op (apply op a₀ b₀) (apply op a₁ b₁) ≤
      1 + sizePotential op a₀ a₁ + sizePotential op b₀ b₁ := by
  cases op <;> cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

theorem depthPotential_apply (op : Op) (a₀ a₁ b₀ b₁ : Bool) :
    depthPotential op (apply op a₀ b₀) (apply op a₁ b₁) ≤
      1 + max (depthPotential op a₀ a₁) (depthPotential op b₀ b₁) := by
  cases op <;> cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

theorem size_potential {op : Op} {n : Nat} (t : Term op n) :
    sizePotential op (eval (fun _ => false) t) (eval (fun _ => true) t) ≤
      size t := by
  induction t with
  | var i => cases op <;> exact Nat.le_refl 0
  | app l r ihl ihr =>
      have h := sizePotential_apply op
        (eval (fun _ => false) l) (eval (fun _ => true) l)
        (eval (fun _ => false) r) (eval (fun _ => true) r)
      simp only [eval, size]
      omega

theorem depth_potential {op : Op} {n : Nat} (t : Term op n) :
    depthPotential op (eval (fun _ => false) t) (eval (fun _ => true) t) ≤
      depth t := by
  induction t with
  | var i => cases op <;> exact Nat.le_refl 0
  | app l r ihl ihr =>
      have h := depthPotential_apply op
        (eval (fun _ => false) l) (eval (fun _ => true) l)
        (eval (fun _ => false) r) (eval (fun _ => true) r)
      simp only [eval, depth]
      omega

theorem formula_lower_bound {op : Op} {n : Nat} (t : Term op n)
    (h : Tautology t) : formulaCost op ≤ size t := by
  have hp := size_potential t
  rw [h (fun _ => false), h (fun _ => true)] at hp
  cases op <;> exact hp

theorem depth_lower_bound {op : Op} {n : Nat} (t : Term op n)
    (h : Tautology t) : depthCost op ≤ depth t := by
  have hp := depth_potential t
  rw [h (fun _ => false), h (fun _ => true)] at hp
  cases op <;> exact hp

/-- Every witness uses just one chosen variable, from any nonempty dimension. -/
def witness (op : Op) {n : Nat} (i : Fin n) : Term op n :=
  match op with
  | .nor => .app (.app (.var i) (.app (.var i) (.var i)))
      (.app (.var i) (.app (.var i) (.var i)))
  | .nand => .app (.var i) (.app (.var i) (.var i))
  | .xnor => .app (.var i) (.var i)
  | .implies => .app (.var i) (.var i)
  | .revImplies => .app (.var i) (.var i)
  | .top => .app (.var i) (.var i)

theorem witness_tautology (op : Op) {n : Nat} (i : Fin n) :
    Tautology (witness op i) := by
  intro v
  cases op <;> cases h : v i <;> simp [witness, eval, apply, h]

theorem witness_size (op : Op) {n : Nat} (i : Fin n) :
    size (witness op i) = formulaCost op := by
  cases op <;> rfl

theorem witness_depth (op : Op) {n : Nat} (i : Fin n) :
    depth (witness op i) = depthCost op := by
  cases op <;> rfl

theorem witness_leaves (op : Op) {n : Nat} (i : Fin n) :
    leaves (witness op i) = formulaCost op + 1 := by
  rw [leaves_eq_size_add_one, witness_size]

/-- Exact simultaneous formula/depth minima over every nonempty finite input set. -/
theorem singleton_minima (op : Op) (n : Nat) (hn : 0 < n) :
    (∀ t : Term op n, Tautology t → formulaCost op ≤ size t) ∧
    (∀ t : Term op n, Tautology t → depthCost op ≤ depth t) ∧
    (∃ t : Term op n, Tautology t ∧ size t = formulaCost op ∧
      depth t = depthCost op) := by
  refine ⟨fun t h => formula_lower_bound t h,
    fun t h => depth_lower_bound t h, ?_⟩
  exact ⟨witness op ⟨0, hn⟩, witness_tautology op ⟨0, hn⟩,
    witness_size op ⟨0, hn⟩, witness_depth op ⟨0, hn⟩⟩

end FIG22.Tree
