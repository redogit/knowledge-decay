import Interface

/-!
Finite local certificates for the lower bounds and obstructions in Theorem 2.
The certificates hold on maximal allowed bases; restricting the basis preserves
them. Their induction consequences apply to every finite formula and DAG.
-/
namespace FIG22.Basis.TheoremTwo

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Unbounded formula size and formula depth lower bounds. -/
def LowerCosts (α : Type) (B : List Op) (f d : Nat) : Prop :=
  (∀ t : Formula α, t.allowed B → t.tautology → f ≤ t.size) ∧
  (∀ t : Formula α, t.allowed B → t.tautology → d ≤ t.depth)

/-- Unbounded obstructions for formulas and shared circuits. -/
def BlockedCosts (α : Type) (B : List Op) : Prop :=
  (∀ t : Formula α, t.allowed B → ¬t.tautology) ∧
  (∀ c : Dag α, c.Allowed B → ¬c.IsTrue)

def weight (z n o : Nat) : Unary → Nat
  | .zero => z
  | .var => 0
  | .neg => n
  | .one => o

theorem term_allowed_of_subset {B M : List Op} (hsub : B ⊆ M)
    (t : Term) (ha : t.allowed B) : t.allowed M := by
  induction t with
  | leaf => trivial
  | gate h a b ia ib => exact ⟨hsub ha.1, ia ha.2.1, ib ha.2.2⟩

theorem lower_of_certificates {α : Type} {B M : List Op} {f d : Nat}
    {fw dw : Unary → Nat} (hsub : B ⊆ M)
    (hf : FormulaValid M fw) (hd : DepthValid M dw)
    (hfc : fw .one = f) (hdc : dw .one = d) : LowerCosts α B f d := by
  constructor
  · intro t ha ht
    have h := formula_lower hf t.diagonal
      (term_allowed_of_subset hsub t.diagonal (t.diagonal_allowed ha))
    simpa only [t.tautology_diagonal ht, hfc, Formula.diagonal_size] using h
  · intro t ha ht
    have h := depth_lower hd t.diagonal
      (term_allowed_of_subset hsub t.diagonal (t.diagonal_allowed ha))
    simpa only [t.tautology_diagonal ht, hdc, Formula.diagonal_depth] using h

theorem blocked_of_certificate {α : Type} {B M : List Op}
    {s : Unary → Bool} (hsub : B ⊆ M)
    (hc : ClosureValid M s) (ho : s .one = false) : BlockedCosts α B := by
  have hb : Blocked B := by
    intro t ha he
    have hs := closure_sound hc t (term_allowed_of_subset hsub t ha)
    rw [he, ho] at hs
    contradiction
  exact ⟨fun t ha => blocked_over hb t ha,
    fun c ha => c.blocked_of_formula hb ha⟩

/-- A zero-gate output is a free variable and is never a tautology. -/
theorem lower_one (α : Type) (B : List Op) : LowerCosts α B 1 1 := by
  constructor
  · intro t ha ht
    cases t with
    | leaf x => have h := ht (fun _ => false); simp [Formula.eval] at h
    | gate h a b => simp [Formula.size]; omega
  · intro t ha ht
    cases t with
    | leaf x => have h := ht (fun _ => false); simp [Formula.eval] at h
    | gate h a b => simp [Formula.depth]

theorem two_formula_certificate :
    FormulaValid [0,1,2,3,4,5,6,7,8,10,12,14] (weight 1 1 2) := by decide

theorem two_depth_certificate :
    DepthValid [0,1,2,3,4,5,6,7,8,10,12,14] (weight 1 1 2) := by decide

theorem lower_two {α : Type} {B : List Op}
    (hsub : B ⊆ [0,1,2,3,4,5,6,7,8,10,12,14]) : LowerCosts α B 2 2 :=
  lower_of_certificates hsub two_formula_certificate two_depth_certificate rfl rfl

theorem three_two_formula_certificate :
    FormulaValid [0,1,2,3,4,5,8] (weight 1 1 3) := by decide

theorem three_two_depth_certificate :
    DepthValid [0,1,2,3,4,5,8] (weight 1 1 2) := by decide

theorem lower_three_two {α : Type} {B : List Op}
    (hsub : B ⊆ [0,1,2,3,4,5,8]) : LowerCosts α B 3 2 :=
  lower_of_certificates hsub three_two_formula_certificate three_two_depth_certificate rfl rfl

theorem three_three_formula_certificate :
    FormulaValid [1,3,5,8,10,12] (weight 2 1 3) := by decide

theorem three_three_depth_certificate :
    DepthValid [1,3,5,8,10,12] (weight 2 1 3) := by decide

theorem lower_three_three {α : Type} {B : List Op}
    (hsub : B ⊆ [1,3,5,8,10,12]) : LowerCosts α B 3 3 :=
  lower_of_certificates hsub three_three_formula_certificate three_three_depth_certificate rfl rfl

theorem five_three_formula_certificate :
    FormulaValid [1,3,5,8] (weight 2 1 5) := by decide

theorem five_three_depth_certificate :
    DepthValid [1,3,5,8] (weight 2 1 3) := by decide

theorem lower_five_three {α : Type} {B : List Op}
    (hsub : B ⊆ [1,3,5,8]) : LowerCosts α B 5 3 :=
  lower_of_certificates hsub five_three_formula_certificate five_three_depth_certificate rfl rfl

def zeroOrVar : Unary → Bool
  | .zero | .var => true
  | .neg | .one => false

def varOrNeg : Unary → Bool
  | .var | .neg => true
  | .zero | .one => false

theorem no_neg_closure_certificate : ClosureValid [0,1,2,3,4,5,6,7] zeroOrVar := by decide

theorem final_closure_certificate : ClosureValid [3,5,10,12] varOrNeg := by decide

theorem blocked_no_neg {α : Type} {B : List Op}
    (hsub : B ⊆ [0,1,2,3,4,5,6,7]) : BlockedCosts α B :=
  blocked_of_certificate hsub no_neg_closure_certificate rfl

theorem blocked_final {α : Type} {B : List Op}
    (hsub : B ⊆ [3,5,10,12]) : BlockedCosts α B :=
  blocked_of_certificate hsub final_closure_certificate rfl

end
end FIG22.Basis.TheoremTwo
