import Interface

/-!
Constructive upper witnesses for the ordered arbitrary-basis classification.
The witnesses come from kernel-checked singleton/pair rows and are admitted
into a larger basis solely through membership; order and duplicates do not matter.
-/
namespace FIG22.Basis.TheoremTwo

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Separate witnesses attain each of formula size, reachable DAG size and depth. -/
def UpperCosts (α : Type) (B : List Op) (f d : Nat) : Prop :=
  (∃ t : Formula α, t.allowed B ∧ t.tautology ∧ t.size = f) ∧
  (∃ c : Dag α, c.Allowed B ∧ c.IsTrue ∧ c.reachableCount = d) ∧
  (∃ t : Formula α, t.allowed B ∧ t.tautology ∧ t.depth = d)

theorem formula_allowed_mono {α : Type} {A B : List Op}
    (h : A ⊆ B) (t : Formula α) (ht : t.allowed A) : t.allowed B := by
  induction t with
  | leaf x => trivial
  | gate op a b ia ib => exact ⟨h ht.1, ia ht.2.1, ib ht.2.2⟩

theorem dag_allowed_mono {α : Type} {A B : List Op}
    (h : A ⊆ B) (c : Dag α) (hc : c.Allowed A) : c.Allowed B := by
  intro i
  exact h (hc i)

theorem upper_of_row {α : Type} (x : α) {B : List Op} {r : Row}
    (hr : r ∈ rows) (hg : r.generates = true) (hsub : r.basis ⊆ B) :
    UpperCosts α B r.formulaCost r.depthCost := by
  have h := every_generating_row_all_costs x hr hg
  rcases h.1.1 with ⟨t, hta, htt, htc⟩
  rcases h.2.1.1 with ⟨c, hca, hct, hcc⟩
  rcases h.2.2.1 with ⟨u, hua, hut, huc⟩
  exact ⟨⟨t, formula_allowed_mono hsub t hta, htt, htc⟩,
    ⟨c, dag_allowed_mono hsub c hca, hct, hcc⟩,
    ⟨u, formula_allowed_mono hsub u hua, hut, huc⟩⟩

theorem upper_one {α : Type} (x : α) (B : List Op)
    (h : (9 : Op) ∈ B ∨ (11 : Op) ∈ B ∨ (13 : Op) ∈ B ∨ (15 : Op) ∈ B) :
    UpperCosts α B 1 1 := by
  rcases h with h | h | h | h
  ·
    exact upper_of_row x (r := row009) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 9 := by simpa [row009] using hm
          subst op; exact h)
  ·
    exact upper_of_row x (r := row011) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 11 := by simpa [row011] using hm
          subst op; exact h)
  ·
    exact upper_of_row x (r := row013) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 13 := by simpa [row013] using hm
          subst op; exact h)
  ·
    exact upper_of_row x (r := row015) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 15 := by simpa [row015] using hm
          subst op; exact h)

theorem upper_two {α : Type} (x : α) (B : List Op)
    (hn : (8 : Op) ∈ B ∨ (10 : Op) ∈ B ∨ (12 : Op) ∈ B ∨ (14 : Op) ∈ B)
    (h : (14 : Op) ∈ B ∨ (6 : Op) ∈ B ∨ (7 : Op) ∈ B ∨
      (((10 : Op) ∈ B ∨ (12 : Op) ∈ B) ∧
       ((0 : Op) ∈ B ∨ (2 : Op) ∈ B ∨ (4 : Op) ∈ B ∨ (6 : Op) ∈ B))) :
    UpperCosts α B 2 2 := by
  rcases h with h | h | h | ⟨hl, hz⟩
  ·
    exact upper_of_row x (r := row014) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 14 := by simpa [row014] using hm
          subst op; exact h)
  · rcases hn with hn | hn | hn | hn
    ·
      exact upper_of_row x (r := row092) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 6 ∨ op = 8 := by simpa [row092] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row094) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 6 ∨ op = 10 := by simpa [row094] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row096) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 6 ∨ op = 12 := by simpa [row096] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row098) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 6 ∨ op = 14 := by simpa [row098] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
  · rcases hn with hn | hn | hn | hn
    ·
      exact upper_of_row x (r := row100) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 7 ∨ op = 8 := by simpa [row100] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row102) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 7 ∨ op = 10 := by simpa [row102] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row104) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 7 ∨ op = 12 := by simpa [row104] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
    ·
      exact upper_of_row x (r := row106) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 7 ∨ op = 14 := by simpa [row106] using hm
            rcases he with he | he
            · subst op; exact h
            · subst op; exact hn)
  · rcases hl with hl | hl
    · rcases hz with hz | hz | hz | hz
      ·
        exact upper_of_row x (r := row025) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 0 ∨ op = 10 := by simpa [row025] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row052) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 2 ∨ op = 10 := by simpa [row052] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row075) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 4 ∨ op = 10 := by simpa [row075] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row094) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 6 ∨ op = 10 := by simpa [row094] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
    · rcases hz with hz | hz | hz | hz
      ·
        exact upper_of_row x (r := row027) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 0 ∨ op = 12 := by simpa [row027] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row054) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 2 ∨ op = 12 := by simpa [row054] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row077) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 4 ∨ op = 12 := by simpa [row077] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)
      ·
        exact upper_of_row x (r := row096) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
          (by intro op hm; have he : op = 6 ∨ op = 12 := by simpa [row096] using hm
              rcases he with he | he
              · subst op; exact hz
              · subst op; exact hl)

theorem upper_three_two {α : Type} (x : α) (B : List Op)
    (hn : (8 : Op) ∈ B)
    (hz : (0 : Op) ∈ B ∨ (2 : Op) ∈ B ∨ (4 : Op) ∈ B) :
    UpperCosts α B 3 2 := by
  rcases hz with hz | hz | hz
  ·
    exact upper_of_row x (r := row023) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 0 ∨ op = 8 := by simpa [row023] using hm
          rcases he with he | he
          · subst op; exact hz
          · subst op; exact hn)
  ·
    exact upper_of_row x (r := row050) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 2 ∨ op = 8 := by simpa [row050] using hm
          rcases he with he | he
          · subst op; exact hz
          · subst op; exact hn)
  ·
    exact upper_of_row x (r := row073) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
      (by intro op hm; have he : op = 4 ∨ op = 8 := by simpa [row073] using hm
          rcases he with he | he
          · subst op; exact hz
          · subst op; exact hn)

theorem upper_three_three {α : Type} (x : α) (B : List Op)
    (hl : (10 : Op) ∈ B ∨ (12 : Op) ∈ B)
    (hn : (8 : Op) ∈ B ∨ (1 : Op) ∈ B) :
    UpperCosts α B 3 3 := by
  rcases hl with hl | hl
  · rcases hn with hn | hn
    ·
      exact upper_of_row x (r := row109) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 8 ∨ op = 10 := by simpa [row109] using hm
            rcases he with he | he
            · subst op; exact hn
            · subst op; exact hl)
    ·
      exact upper_of_row x (r := row039) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 1 ∨ op = 10 := by simpa [row039] using hm
            rcases he with he | he
            · subst op; exact hn
            · subst op; exact hl)
  · rcases hn with hn | hn
    ·
      exact upper_of_row x (r := row111) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 8 ∨ op = 12 := by simpa [row111] using hm
            rcases he with he | he
            · subst op; exact hn
            · subst op; exact hl)
    ·
      exact upper_of_row x (r := row041) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
        (by intro op hm; have he : op = 1 ∨ op = 12 := by simpa [row041] using hm
            rcases he with he | he
            · subst op; exact hn
            · subst op; exact hl)

theorem upper_five_three {α : Type} (x : α) (B : List Op)
    (hn : (8 : Op) ∈ B) : UpperCosts α B 5 3 := by
  exact upper_of_row x (r := row008) (by simp only [rows, List.mem_cons, eq_self, true_or, or_true]) rfl
    (by intro op hm; have he : op = 8 := by simpa [row008] using hm
        subst op; exact hn)

end
end FIG22.Basis.TheoremTwo
