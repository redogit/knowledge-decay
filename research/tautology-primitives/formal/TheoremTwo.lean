import TheoremTwoUpper
import TheoremTwoLower

/-!
# The complete ordered classification for arbitrary binary Boolean bases

This theorem quantifies over every list of the sixteen operations, including
empty lists, arbitrary ordering and repetitions. Local certificates establish
unbounded lower bounds; existing singleton/pair witnesses supply upper bounds
by inclusion. No enumeration bound on formulas, DAGs or basis cardinality is used.
-/
namespace FIG22.Basis.TheoremTwo

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev HasC (B : List Op) := (9 : Op) ∈ B ∨ 11 ∈ B ∨ 13 ∈ B ∨ 15 ∈ B
abbrev HasN (B : List Op) := (8 : Op) ∈ B ∨ 10 ∈ B ∨ 12 ∈ B ∨ 14 ∈ B
abbrev HasZ (B : List Op) := (0 : Op) ∈ B ∨ 2 ∈ B ∨ 4 ∈ B ∨ 6 ∈ B
abbrev HasL (B : List Op) := (10 : Op) ∈ B ∨ 12 ∈ B
abbrev HasTwo (B : List Op) := (14 : Op) ∈ B ∨ 6 ∈ B ∨ 7 ∈ B ∨ (HasL B ∧ HasZ B)
abbrev HasThreeTwo (B : List Op) := (8 : Op) ∈ B ∧ HasZ B
abbrev HasThreeThree (B : List Op) := HasL B ∧ ((8 : Op) ∈ B ∨ 1 ∈ B)

/-- The seven ordered rows, retaining the two different obstruction reasons. -/
inductive Branch where
  | one | noNeg | two | threeTwo | threeThree | fiveThree | final
  deriving DecidableEq, Repr

/-- The first matching row; every later test is reached only after earlier failure. -/
def classify (B : List Op) : Branch :=
  if HasC B then .one else if ¬HasN B then .noNeg else
  if HasTwo B then .two else if HasThreeTwo B then .threeTwo else
  if HasThreeThree B then .threeThree else
  if (8 : Op) ∈ B then .fiveThree else .final

/-- Each condition explicitly includes the failure of every preceding row. -/
def BranchCondition (B : List Op) : Branch → Prop
  | .one => HasC B
  | .noNeg => ¬HasC B ∧ ¬HasN B
  | .two => ¬HasC B ∧ HasN B ∧ HasTwo B
  | .threeTwo => ¬HasC B ∧ HasN B ∧ ¬HasTwo B ∧ HasThreeTwo B
  | .threeThree => ¬HasC B ∧ HasN B ∧ ¬HasTwo B ∧
      ¬HasThreeTwo B ∧ HasThreeThree B
  | .fiveThree => ¬HasC B ∧ HasN B ∧ ¬HasTwo B ∧
      ¬HasThreeTwo B ∧ ¬HasThreeThree B ∧ (8 : Op) ∈ B
  | .final => ¬HasC B ∧ HasN B ∧ ¬HasTwo B ∧
      ¬HasThreeTwo B ∧ ¬HasThreeThree B ∧ (8 : Op) ∉ B

/-- Ordered conditions determine one and only one selected branch. -/
theorem classify_of_condition (B : List Op) (b : Branch)
    (h : BranchCondition B b) : classify B = b := by
  cases b with
  | one => exact ite_eq_left h
  | noNeg =>
    rcases h with ⟨hc, hn⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_left hn]
  | two =>
    rcases h with ⟨hc, hn, ht⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_right (fun hnot => hnot hn), ite_eq_left ht]
  | threeTwo =>
    rcases h with ⟨hc, hn, ht, hfour⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_right (fun hnot => hnot hn), ite_eq_right ht, ite_eq_left hfour]
  | threeThree =>
    rcases h with ⟨hc, hn, ht, hfour, hf⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_right (fun hnot => hnot hn), ite_eq_right ht, ite_eq_right hfour, ite_eq_left hf]
  | fiveThree =>
    rcases h with ⟨hc, hn, ht, hfour, hf, h8⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_right (fun hnot => hnot hn), ite_eq_right ht, ite_eq_right hfour, ite_eq_right hf, ite_eq_left h8]
  | final =>
    rcases h with ⟨hc, hn, ht, hfour, hf, h8⟩
    unfold classify
    rw [ite_eq_right hc, ite_eq_right (fun hnot => hnot hn), ite_eq_right ht, ite_eq_right hfour, ite_eq_right hf, ite_eq_right h8]

/-- Every basis meets the full ordered condition of its selected row. -/
theorem branch_complete (B : List Op) : BranchCondition B (classify B) := by
  unfold classify
  split
  · rename_i hc; exact hc
  · rename_i hc
    split
    · rename_i hn; exact ⟨hc, hn⟩
    · rename_i hn
      have hn : HasN B := Classical.not_not.mp hn
      split
      · rename_i ht; exact ⟨hc, hn, ht⟩
      · rename_i ht
        split
        · rename_i hfour; exact ⟨hc, hn, ht, hfour⟩
        · rename_i hfour
          split
          · rename_i hf; exact ⟨hc, hn, ht, hfour, hf⟩
          · rename_i hf
            split
            · rename_i h8; exact ⟨hc, hn, ht, hfour, hf, h8⟩
            · rename_i h8; exact ⟨hc, hn, ht, hfour, hf, h8⟩

/-- The classifier is equivalent to the published ordered row conditions. -/
theorem classify_iff (B : List Op) (b : Branch) :
    classify B = b ↔ BranchCondition B b := by
  constructor
  · intro h; rw [← h]; exact branch_complete B
  · exact classify_of_condition B b

/-- Basis order and repeated entries have no effect on the classified costs. -/
theorem classify_congr {A B : List Op} (h : ∀ op, op ∈ A ↔ op ∈ B) :
    classify A = classify B := by
  simp only [classify, HasC, HasN, HasTwo, HasThreeTwo, HasThreeThree,
    HasL, HasZ, h]

/-- All four minima are independently quantified over their entire circuit model. -/
def ExactCosts (α : Type) (B : List Op) (f d : Nat) : Prop :=
  ExactFormulaOver α B f ∧ ExactDagOver α B d ∧ ExactDepthOver α B d ∧
    FIG22.Checked.ExactDagDepthOver α B d

/-- The result associated with an ordered row. -/
def Result (α : Type) (B : List Op) : Branch → Prop
  | .one => ExactCosts α B 1 1
  | .noNeg => BlockedCosts α B
  | .two => ExactCosts α B 2 2
  | .threeTwo => ExactCosts α B 3 2
  | .threeThree => ExactCosts α B 3 3
  | .fiveThree => ExactCosts α B 5 3
  | .final => BlockedCosts α B

theorem exact_of_bounds {α : Type} {B : List Op} {f d : Nat}
    (hu : UpperCosts α B f d) (hl : LowerCosts α B f d) : ExactCosts α B f d := by
  have hf : ExactFormulaOver α B f := ⟨hu.1, hl.1⟩
  have hd : ExactDepthOver α B d := ⟨hu.2.2, hl.2⟩
  have hg : ExactDagOver α B d := by
    refine ⟨hu.2.1, ?_⟩
    intro c ha ht
    exact Nat.le_trans (hl.2 c.formula (c.unfold_allowed ha _ _) ht) c.depth_le_reachable
  exact ⟨hf, hg, hd, FIG22.Checked.dag_depth_exact_of_formula_depth hd hg⟩

/-- Exhaustiveness of the ordered operation encoding is checked only once. -/
theorem op_exhaustive (h : Op) :
    h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨
    h = 8 ∨ h = 9 ∨ h = 10 ∨ h = 11 ∨ h = 12 ∨ h = 13 ∨ h = 14 ∨ h = 15 := by
  revert h
  decide

theorem subset_noC {B : List Op} (hc : ¬HasC B) :
    B ⊆ [0,1,2,3,4,5,6,7,8,10,12,14] := by
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC]

theorem subset_no_neg {B : List Op} (hc : ¬HasC B) (hn : ¬HasN B) :
    B ⊆ [0,1,2,3,4,5,6,7] := by
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC, HasN]

theorem subset_three_two {B : List Op} (hc : ¬HasC B) (ht : ¬HasTwo B)
    (hz : HasZ B) : B ⊆ [0,1,2,3,4,5,8] := by
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC, HasTwo, HasL, HasZ]

theorem no_z_after_three {B : List Op} (hn : HasN B) (ht : ¬HasTwo B)
    (hfour : ¬HasThreeTwo B) : ¬HasZ B := by
  intro hz
  rcases hn with h8 | h10 | h12 | h14
  · exact hfour ⟨h8, hz⟩
  · exact ht (Or.inr (Or.inr (Or.inr ⟨Or.inl h10, hz⟩)))
  · exact ht (Or.inr (Or.inr (Or.inr ⟨Or.inr h12, hz⟩)))
  · exact ht (Or.inl h14)

theorem subset_three_three {B : List Op} (hc : ¬HasC B) (ht : ¬HasTwo B)
    (hz : ¬HasZ B) : B ⊆ [1,3,5,8,10,12] := by
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC, HasTwo, HasL, HasZ]

theorem subset_five_three {B : List Op} (hc : ¬HasC B) (ht : ¬HasTwo B)
    (hz : ¬HasZ B) (hf : ¬HasThreeThree B) (h8 : (8 : Op) ∈ B) :
    B ⊆ [1,3,5,8] := by
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC, HasTwo, HasL, HasZ, HasThreeThree]

theorem subset_final {B : List Op} (hc : ¬HasC B) (hn : HasN B)
    (ht : ¬HasTwo B) (hz : ¬HasZ B) (hf : ¬HasThreeThree B)
    (h8 : (8 : Op) ∉ B) : B ⊆ [3,5,10,12] := by
  have hl : HasL B := by
    rcases hn with hn | hn | hn | hn
    · contradiction
    · exact Or.inl hn
    · exact Or.inr hn
    · exact False.elim (ht (Or.inl hn))
  intro h hm
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals simp_all [HasC, HasTwo, HasL, HasZ, HasThreeThree]

/-- Theorem 2: exact formula, reachable-DAG and both depth minima for every basis. -/
theorem theorem_two {α : Type} (x : α) (B : List Op) : Result α B (classify B) := by
  unfold classify
  split
  · rename_i hc
    exact exact_of_bounds (upper_one x B hc) (lower_one α B)
  · rename_i hc
    split
    · rename_i hn
      exact blocked_no_neg (subset_no_neg hc hn)
    · rename_i hn
      have hn : HasN B := Classical.not_not.mp hn
      split
      · rename_i ht
        exact exact_of_bounds (upper_two x B hn ht) (lower_two (subset_noC hc))
      · rename_i ht
        split
        · rename_i hfour
          have hz : (0 : Op) ∈ B ∨ 2 ∈ B ∨ 4 ∈ B := by
            rcases hfour.2 with hz | hz | hz | hz
            · exact Or.inl hz
            · exact Or.inr (Or.inl hz)
            · exact Or.inr (Or.inr hz)
            · exact False.elim (ht (Or.inr (Or.inl hz)))
          exact exact_of_bounds (upper_three_two x B hfour.1 hz)
            (lower_three_two (subset_three_two hc ht hfour.2))
        · rename_i hfour
          have hz := no_z_after_three hn ht hfour
          split
          · rename_i hf
            exact exact_of_bounds (upper_three_three x B hf.1 hf.2)
              (lower_three_three (subset_three_three hc ht hz))
          · rename_i hf
            split
            · rename_i h8
              exact exact_of_bounds (upper_five_three x B h8)
                (lower_five_three (subset_five_three hc ht hz hf h8))
            · rename_i h8
              exact blocked_final (subset_final hc hn ht hz hf h8)

/-- Exact costs or unbounded impossibility for a specified ordered row. -/
theorem ordered_row {α : Type} (x : α) (B : List Op) (b : Branch)
    (h : BranchCondition B b) : Result α B b := by
  have hc := (classify_iff B b).mpr h
  simpa only [hc] using theorem_two x B

/-- A canonical list containing every operation once. -/
def allOps : List Op := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

theorem mem_allOps (h : Op) : h ∈ allOps := by
  rcases op_exhaustive h with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
  all_goals subst h
  all_goals decide

/-- Represent any mathematical subset, without requiring a supplied decision procedure. -/
noncomputable def basisOf (P : Op → Prop) : List Op := by
  classical
  exact allOps.filter (fun h => decide (P h))

theorem mem_basisOf (P : Op → Prop) (h : Op) : h ∈ basisOf P ↔ P h := by
  classical
  simp [basisOf, mem_allOps]

/-- Predicate subsets and arbitrary list representations have the same classifier. -/
theorem classify_normalize (B : List Op) :
    classify (basisOf (fun h => h ∈ B)) = classify B :=
  classify_congr (fun h => mem_basisOf _ h)

/-- Theorem 2 also quantifies directly over every subset of all binary operations. -/
theorem theorem_two_subset {α : Type} (x : α) (P : Op → Prop) :
    Result α (basisOf P) (classify (basisOf P)) :=
  theorem_two x (basisOf P)

end
end FIG22.Basis.TheoremTwo
