import TheoremTwo

/-! Consequences of the exhaustive classification, including the missing cost four. -/
namespace FIG22.Basis.TheoremTwo

noncomputable section

/-- Every nonempty variable type and every binary basis has one of these outcomes. -/
theorem complete {α : Type} (x : α) (B : List Op) :
    BlockedCosts α B ∨ ExactCosts α B 1 1 ∨ ExactCosts α B 2 2 ∨
      ExactCosts α B 3 2 ∨ ExactCosts α B 3 3 ∨ ExactCosts α B 5 3 := by
  have h := theorem_two x B
  cases hc : classify B with
  | one => exact Or.inr (Or.inl (by simpa only [hc, Result] using h))
  | noNeg => exact Or.inl (by simpa only [hc, Result] using h)
  | two => exact Or.inr (Or.inr (Or.inl (by simpa only [hc, Result] using h)))
  | threeTwo => exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hc, Result] using h))))
  | threeThree => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hc, Result] using h)))))
  | fiveThree => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hc, Result] using h)))))
  | final => exact Or.inl (by simpa only [hc, Result] using h)

theorem formula_minimum_unique {α : Type} {B : List Op} {m n : Nat}
    (hm : ExactFormulaOver α B m) (hn : ExactFormulaOver α B n) : m = n := by
  obtain ⟨tm, hma, hmt, hmc⟩ := hm.1
  obtain ⟨tn, hna, hnt, hnc⟩ := hn.1
  have hmn := hm.2 tn hna hnt
  have hnm := hn.2 tm hma hmt
  omega

theorem depth_minimum_unique {α : Type} {B : List Op} {m n : Nat}
    (hm : ExactDepthOver α B m) (hn : ExactDepthOver α B n) : m = n := by
  obtain ⟨tm, hma, hmt, hmc⟩ := hm.1
  obtain ⟨tn, hna, hnt, hnc⟩ := hn.1
  have hmn := hm.2 tn hna hnt
  have hnm := hn.2 tm hma hmt
  omega

theorem dag_minimum_unique {α : Type} {B : List Op} {m n : Nat}
    (hm : ExactDagOver α B m) (hn : ExactDagOver α B n) : m = n := by
  obtain ⟨cm, hma, hmt, hmc⟩ := hm.1
  obtain ⟨cn, hna, hnt, hnc⟩ := hn.1
  have hmn := hm.2 cn hna hnt
  have hnm := hn.2 cm hma hmt
  omega

theorem dag_depth_minimum_unique {α : Type} {B : List Op} {m n : Nat}
    (hm : FIG22.Checked.ExactDagDepthOver α B m)
    (hn : FIG22.Checked.ExactDagDepthOver α B n) : m = n := by
  obtain ⟨cm, hma, hmt, hmc⟩ := hm.1
  obtain ⟨cn, hna, hnt, hnc⟩ := hn.1
  have hmn := hm.2 cn hna hnt
  have hnm := hn.2 cm hma hmt
  omega

/-- Formula optimum four is impossible for every binary basis in this model. -/
theorem no_formula_four {α : Type} (x : α) (B : List Op) :
    ¬ExactFormulaOver α B 4 := by
  intro h4
  rcases complete x B with hb | h | h | h | h | h
  · obtain ⟨t, ha, ht, _⟩ := h4.1
    exact hb.1 t ha ht
  all_goals have he := formula_minimum_unique h4 h.1; omega

/-- Existence alone forces finite optimal costs within the sharp global bounds. -/
theorem every_reachable_cost {α : Type} (x : α) (B : List Op)
    (ht : ∃ t : Formula α, t.allowed B ∧ t.tautology) :
    ∃ f d, f ≤ 5 ∧ d ≤ 3 ∧ f ≠ 4 ∧ ExactCosts α B f d := by
  rcases complete x B with hb | h | h | h | h | h
  · obtain ⟨t, ha, ht⟩ := ht
    exact False.elim (hb.1 t ha ht)
  · exact ⟨1, 1, by decide, by decide, by decide, h⟩
  · exact ⟨2, 2, by decide, by decide, by decide, h⟩
  · exact ⟨3, 2, by decide, by decide, by decide, h⟩
  · exact ⟨3, 3, by decide, by decide, by decide, h⟩
  · exact ⟨5, 3, by decide, by decide, by decide, h⟩

/-- Independently minimized shared size and formula depth always agree. -/
theorem shared_equals_depth {α : Type} (x : α) (B : List Op) {g d : Nat}
    (hg : ExactDagOver α B g) (hd : ExactDepthOver α B d) : g = d := by
  rcases complete x B with hb | h | h | h | h | h
  · obtain ⟨c, ha, ht, _⟩ := hg.1
    exact False.elim (hb.2 c ha ht)
  all_goals
    have hgc := dag_minimum_unique hg h.2.1
    have hdc := depth_minimum_unique hd h.2.2.1
    omega

/-- Independently minimized shared size and shared depth also always agree. -/
theorem shared_equals_dag_depth {α : Type} (x : α) (B : List Op) {g d : Nat}
    (hg : ExactDagOver α B g) (hd : FIG22.Checked.ExactDagDepthOver α B d) : g = d := by
  rcases complete x B with hb | h | h | h | h | h
  · obtain ⟨c, ha, ht, _⟩ := hg.1
    exact False.elim (hb.2 c ha ht)
  all_goals
    have hgc := dag_minimum_unique hg h.2.1
    have hdc := dag_depth_minimum_unique hd h.2.2.2
    omega

theorem formula_optimum_bound {α : Type} (x : α) (B : List Op) {f : Nat}
    (hf : ExactFormulaOver α B f) : f ≤ 5 ∧ f ≠ 4 := by
  obtain ⟨t, ha, ht, _⟩ := hf.1
  obtain ⟨f', d', hfb, _, hf4, h⟩ := every_reachable_cost x B ⟨t, ha, ht⟩
  have he := formula_minimum_unique hf h.1
  omega

theorem depth_optimum_bound {α : Type} (x : α) (B : List Op) {d : Nat}
    (hd : ExactDepthOver α B d) : d ≤ 3 := by
  obtain ⟨t, ha, ht, _⟩ := hd.1
  obtain ⟨f', d', _, hdb, _, h⟩ := every_reachable_cost x B ⟨t, ha, ht⟩
  have he := depth_minimum_unique hd h.2.2.1
  omega

theorem dag_optimum_bound {α : Type} (x : α) (B : List Op) {g : Nat}
    (hg : ExactDagOver α B g) : g ≤ 3 := by
  obtain ⟨c, ha, ht, _⟩ := hg.1
  obtain ⟨f', d', _, hdb, _, h⟩ := every_reachable_cost x B
    ⟨c.formula, c.unfold_allowed ha _ _, ht⟩
  have he := dag_minimum_unique hg h.2.1
  omega

end
end FIG22.Basis.TheoremTwo
