import Mathlib
open Finset BigOperators

example (f : ℕ → ℕ → ℂ) (m : ℕ) :
  (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
  (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) := by

  -- Define triangular region as filtered over product
  let triangle : Finset (ℕ × ℕ) :=
    (range m ×ˢ range m).filter (λ (i, j) => j ≤ i)

  -- Rewriting the LHS: ∑ i < m, ∑ j ≤ i
  have lhs_eq : (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
      triangle.sum (λ (ij : ℕ × ℕ) => f ij.1 ij.2) := by
    -- Expand outer sum over i
    apply Eq.symm
    apply sum_bij'
    · intro i _ => (range (i + 1)).attach.map (λ j => (i, j))
    · intro i hi => (range (i + 1)).attach.map (λ j => (i, j))
    · intros i _ j _
      simp only [mem_range, mem_attach, mem_map, mem_product, mem_filter]
      exact ⟨j, ⟨i, j⟩, ⟨⟨i < m, j.1 < i + 1⟩, le_of_lt_succ j.2⟩, rfl⟩
    · rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ h
      simp only at h
      injection h with hi hj
      simp [hi, hj]
    · intro ⟨i, j⟩ h
      simp only [mem_filter, mem_product, mem_range] at h
      let j' : {x // x < i + 1} := ⟨j, Nat.lt_succ_of_le h.2⟩
      use i
      use j'
      simp [j'.val, h.1]
      rfl

  -- Rewriting the RHS: ∑ j < m, ∑ i ∈ Ico j m
  have rhs_eq : (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) =
      triangle.sum (λ (ij : ℕ × ℕ) => f ij.1 ij.2) := by
    -- Very similar to the lhs
    apply Eq.symm
    apply sum_bij'
    · intro j _ => (Ico j m).attach.map (λ i => (i, j))
    · intro j hj => (Ico j m).attach.map (λ i => (i, j))
    · intros j _ i _
      simp only [mem_Ico, mem_attach, mem_map, mem_product, mem_filter]
      intro hij
      exact ⟨i, ⟨i.1 < m, hj⟩, hij.1⟩
    · rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ h
      injection h with hi hj
      simp [hi, hj]
    · intro ⟨i, j⟩ h
      simp only [mem_filter, mem_product, mem_range] at h
      let i' : {x // j ≤ x ∧ x < m} := ⟨i, ⟨h.2, h.1.1⟩⟩
      use j
      use i'
      simp [i'.val, h.1.2]
      rfl

  rw [lhs_eq, rhs_eq]

-- import Mathlib

-- -- import Mathlib.Data.Finset.Basic
-- -- import Mathlib.Algebra.BigOperators.Basic
-- -- import Mathlib.Data.Complex.Basic
-- -- import Mathlib.Data.Nat.Interval

-- open Finset BigOperators

-- example (f : ℕ → ℕ → ℂ) (m : ℕ) :
--   (Finset.range m).sum (λ i => (Finset.range (i + 1)).sum (λ j => f i j))
--   = (Finset.range m).sum (λ j => (Finset.Icc j (m - 1)).sum (λ i => f i j)) := by
--   -- We'll use `Finset.sum_comm` on the triangle {(i, j) | i ∈ range m, j ∈ range (i + 1)}
--   #check sum_product'
--   rw [Finset.sum_comm]
--   -- Now we are summing over j ∈ range m, i ∈ Icc j (m - 1)
--   -- because originally j ≤ i < m, so i ∈ [j, m)

--   rfl
--   sorry



-- example (f : ℕ → ℕ → ℂ) (m : ℕ) :
--   (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
--   (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) := by
--   -- We'll rewrite both sides as a filtered sum over i, j ∈ range m
--   have : (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
--     ((range m ×ˢ range m).filter (λ (i, j) => j ≤ i)).sum (λ (i, j) => f i j) := by
--     change ∑ x ∈ (range m), ∑ y ∈ (range (x + 1)), f x y = ((range m ×ˢ range m).filter (λ (i, j) => j ≤ i)).sum (λ (i, j) => f i j)
--     rw [← sum_product' (range m) (range (x + 1)) f ]
--     apply sum_congr rfl
--     intro i hi
--     rw [← sum_filter]
--     congr
--     ext j
--     simp only [mem_range, mem_filter, mem_product, mem_range]
--     constructor
--     · intro hj
--       exact ⟨⟨j < i + 1, hi⟩, le_of_lt_succ hj⟩
--     · intro ⟨⟨_, _⟩, hj⟩
--       exact lt_of_le_of_lt hj (Nat.lt_succ_self i)
--   rw [this]
--   -- Now rewrite RHS in same filtered form with swapped indices
--   have : (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) =
--     ((range m ×ˢ range m).filter (λ (i, j) => j ≤ i)).sum (λ (i, j) => f i j) := by
--     rw [<- sum_product']
--     apply sum_congr rfl
--     intro j hj
--     rw [← sum_filter]
--     congr
--     ext i
--     simp only [mem_range, mem_filter, mem_product, mem_Ico]
--     constructor
--     · intro ⟨h1, h2⟩
--       exact ⟨⟨i < m, hj⟩, h1⟩
--     · intro ⟨⟨_, _⟩, h1⟩
--       exact ⟨h1, Nat.lt_of_lt_of_le ‹j < m› h1⟩
--   rw [this]


-- open Finset BigOperators

-- example (f : ℕ → ℕ → ℂ) (m : ℕ) :
--     (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
--     (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) := by

--   -- Let S := { (i, j) ∈ range m × range m | j ≤ i }
--   let S := (range m ×ˢ range m).filter (λ (i, j) => j ≤ i)

--   -- Left side as a filtered product
--   have lhs_eq : (range m).sum (λ i => (range (i + 1)).sum (λ j => f i j)) =
--     S.sum (λ (i, j) => f i j) := by
--     rw [← sum_product']
--     apply sum_congr rfl
--     intro i hi
--     rw [← sum_filter]
--     congr
--     ext j
--     simp only [mem_range, mem_filter, mem_product]
--     constructor
--     · intro hj
--       exact ⟨⟨hi, lt_of_lt_succ hj⟩, le_of_lt_succ hj⟩
--     · rintro ⟨⟨hi, _⟩, hj⟩
--       exact lt_of_le_of_lt hj (Nat.lt_succ_self i)

--   -- Right side as same filtered product
--   have rhs_eq : (range m).sum (λ j => (Ico j m).sum (λ i => f i j)) =
--     S.sum (λ (i, j) => f i j) := by
--     rw [← sum_product']
--     apply sum_congr rfl
--     intro j hj
--     rw [← sum_filter]
--     congr
--     ext i
--     simp only [mem_range, mem_filter, mem_product, mem_Ico]
--     constructor
--     · intro ⟨hij, him⟩
--       exact ⟨⟨him, hj⟩, hij⟩
--     · rintro ⟨⟨him, _⟩, hij⟩
--       exact ⟨hij, him⟩

--   rw [lhs_eq, rhs_eq]
