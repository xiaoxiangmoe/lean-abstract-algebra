import tactic
import group_theory.coset
import group_theory.quotient_group
import group_theory.index
import group_theory.finiteness
import data.setoid.partition

namespace chapter2.section2

variables {G : Type*} [group G]

-- 定义 2-1
-- #check subgroup.one_mem'
-- #check subgroup.mul_mem'
-- #check subgroup.inv_mem'
-- #check subgroup.one_mem
-- #check subgroup.mul_mem
-- #check subgroup.inv_mem
-- variables  (H : subgroup G)
def subgroup_trans_2_1 (H : subgroup G) (K : subgroup H) := subgroup.map H.subtype K

namespace lemma_2_1

-- (H_sub_G: H ⊆ set.univ)
def lemma_2_1_1 (H: set G) (H_n_empty: H.nonempty) (h1 : ∀ a b, a ∈ H → b ∈ H → (a * b ∈ H)) (h2 : ∀ a, a ∈ H → a⁻¹ ∈ H) : subgroup G :=
{
  carrier := H,
  one_mem' := begin
    induction H_n_empty with a a_in_H,
    have a_inv_in_H := h2 a a_in_H,
    have := h1 _ _ a_in_H a_inv_in_H,
    rw mul_inv_self at this,
    exact this,
  end,
  mul_mem' := h1,
  inv_mem' := h2,
}

def lemma_2_1_2 (H: set G) (H_n_empty: H.nonempty) (h : ∀ a b, a ∈ H → b ∈ H → (a * b⁻¹ ∈ H)) : subgroup G :=
begin
  have one_mem: (1 : G) ∈ H := begin
    cases H_n_empty with a a_in_H,
    have := h a a a_in_H a_in_H,
    rw mul_inv_self at this,
    exact this
  end,

  exact {
    carrier := H,
    one_mem' := one_mem,
    mul_mem' := begin
      intros a b ha hb,
      replace hb := h _ _ one_mem hb,
      rw one_mul at hb,
      have := h _ _ ha hb,
      rw inv_inv at this,
      exact this,
    end,
    inv_mem' := begin
      intros a ha,
      have := h _ _ one_mem ha,
      rw one_mul at this,
      exact this,
    end,
  },
end

def lemma_2_1_3 (H: finset G) (s_nonempty: H.nonempty)  (h1 : ∀ a b, a ∈ H → b ∈ H → (a * b ∈ H)) : subgroup G := lemma_2_1_1 H (finset.coe_nonempty.mpr s_nonempty) h1 (λ x h_x, begin
  have my_set_map: set.maps_to (λ (n : ℕ), x ^ (n + 1)) set.univ H := begin
    intros n hn,
    simp,
    induction n,
    { simp, assumption },
    {
      specialize n_ih (set.mem_univ n_n),
      specialize h1 _ _ n_ih h_x,
      rw pow_add, rw pow_one,
      exact h1,
    }
  end,
  obtain ⟨r, -, s, -, H_r_neq_s, H4⟩ := set.infinite.exists_ne_map_eq_of_maps_to set.infinite_univ my_set_map (finset.finite_to_set H),
  clear my_set_map,
  simp at H4,
  wlog H_r_s : s < r, { exact (ne.symm H_r_neq_s).lt_or_lt }, clear H_r_neq_s,

  have h:= pow_mul_pow_sub x (nat.succ_le_succ (le_of_lt H_r_s)),
  rw H4 at h,
  clear H4,
  simp at h,
  have h1: r - s > 0 := tsub_pos_of_lt H_r_s,

  have h2: ∀ x , x > 0 → ∃ (t : ℕ), t + 1 = x := begin intros x hx, induction x, linarith, use x_n, end,
  replace h2 := h2 _ h1,
  obtain ⟨t, h2⟩ := h2,
  clear h1,
  rw ← h2 at h,
  clear h2 H_r_s r s,
  have h3: ∀ u, x ^ (u + 1) ∈ H := begin
    intro u,
    induction u,
    { simpa using h_x },
    {
      have := h1 _ _ u_ih h_x,
      rw [pow_add, pow_one],
      exact this,
    },
  end,

  convert_to x ^ t ∈ ↑H,
  {
    rw [pow_add, pow_one] at h,
    rw mul_eq_one_iff_eq_inv at h,
    exact eq.symm h,
  },

  have h4 := h3 (t + t),
  rw [add_assoc,pow_add] at h4,
  rw h at h4,
  rw mul_one at h4,
  exact h4,
end)

end lemma_2_1

-- #check quotient_group.subgroup.has_quotient


-- #check set.center
-- #check subgroup.center
-- 命题2-2
def lemma_2_2 : subgroup G :=
{
  carrier := set.center G,
  one_mem' := begin
    dunfold set.center,
    dunfold has_mem.mem set.mem set_of,
    simp,
  end,
  mul_mem' := begin
    dunfold set.center,
    dunfold has_mem.mem set.mem set_of,
    intros a b ha hb g,
    exact by calc
      g * (a * b) = (g * a) * b : by group
      ...         = (a * g) * b : by rw ha
      ...         = a * (g * b) : by group
      ...         = a * (b * g) : by rw hb
      ...         = a * b * g : by group
  end,
  inv_mem' := begin
    dunfold set.center,
    dunfold has_mem.mem set.mem set_of,
    intros g h a,
    specialize h a,
    rw ← eq_mul_inv_iff_mul_eq at h,
    rw mul_assoc at h,
    rw ← inv_mul_eq_iff_eq_mul at h,
    rw h,
  end,
}


-- 定义2-3
-- #check subgroup.mem_closure
-- Schreier's lemma
-- https://leanprover-community.github.io/mathlib_docs/group_theory/schreier.html#subgroup.closure_mul_image_eq
-- #check subgroup.closure_mul_image_eq

-- 命题2-3
-- lemma lemma_2_3 (S : set G) : ∃ (S': subgroup G),  subgroup.closure S = S' ∧ S'.carrier = { |}
-- TODO: 做不来

-- 定义2-4
-- #check is_of_fin_order
-- #check order_of
-- lemma lemma_2_4   (a : G) (h : is_of_fin_order a) : subgroup.closure ({ a } : set G) = subgroup.closure ({ a } : set G)  := begin
--   induction h,
-- end

-- 定义2-5
-- #check @left_coset


lemma xz_2_1_1_r (H : subgroup G) (a b: G) : (right_coset ↑H a = right_coset ↑H b) ↔ a * b⁻¹ ∈ H :=
begin
  dunfold right_coset set.image,
  rw set.ext_iff,
  simp,
  split,
  {
    intro h,
    replace h := (h a).mp,
    replace h := h ⟨1, one_mem H, by group⟩,
    rcases h with ⟨g, hg, hg_eq⟩,
    rw ← eq_mul_inv_iff_mul_eq at hg_eq,
    rw hg_eq at *,
    assumption,
  },
  {
    intros h1 g,
    split,
    {
      rintros ⟨h, hh, hh_eq⟩,
      replace hh_eq := eq_mul_inv_of_mul_eq hh_eq,
      rw hh_eq at *, clear hh_eq h,
      use g * b⁻¹,
      have := mul_mem hh h1,
      simpa [mul_assoc] using this,
    },
    {
      rintros ⟨h, hh, hh_eq⟩,
      replace hh_eq := eq_mul_inv_of_mul_eq hh_eq,
      rw hh_eq at *, clear hh_eq h,
      use g * a⁻¹,
      replace h1 := inv_mem h1,
      simp at h1,
      have := mul_mem hh h1,
      simpa [mul_assoc] using this,
    }
  }
end

-- 性质 _2_1_1_l
-- #check left_coset_eq_iff
lemma my_left_coset_eq_iff (H : subgroup G) {a b: G} : (left_coset a H = left_coset b H) ↔ a⁻¹ * b ∈ H :=
begin
  dunfold left_coset,
  dunfold set.image,
  -- have := left_coset_equivalence_rel ↑H,
  -- unfold equivalence left_coset_equivalence reflexive symmetric transitive at this,
  split,
  {
    rw set.ext_iff,
    simp,
    intro h,
    replace h := (h a).mp,
    replace h := h ⟨1, one_mem H, by group⟩,
    rcases h with ⟨g, hg, hg_eq⟩,
    rw ← eq_inv_mul_iff_mul_eq at hg_eq,
    rw hg_eq at hg, clear hg_eq,
    simpa using inv_mem hg,
  },
  {
    intro h1,
    ext g,
    split;simp,
    {
      rintros h hh rfl,
      use b⁻¹ * a * h,
      refine ⟨_, by group⟩,
      replace h1 := inv_mem h1,
      simp at h1,
      exact mul_mem h1 hh,
    },
    {
      rintros h hh rfl,
      use a⁻¹ * b * h,
      refine ⟨_, by group⟩,
      exact mul_mem h1 hh,
    }
  }
end

def xz_2 (H : subgroup G) (a b: G) : (right_coset ↑H a ≃ right_coset ↑H b) :=
{
  to_fun := begin
    rintro ⟨c, hc⟩,
    use c * a⁻¹ * b,
    rcases hc with ⟨d,hd,rfl⟩,
    use d,
    exact ⟨hd, by group⟩,
  end,
  inv_fun := begin
    -- dunfold right_coset set.image,
    rintro ⟨c, hc⟩,
    -- simp at *,
    use c * b⁻¹ * a,
    rcases hc with ⟨d,hd,rfl⟩,
    use d,
    exact ⟨hd, by group⟩,
  end,
  left_inv := begin
    rw function.left_inverse,
    simp,
  end,
  right_inv :=begin
    rw function.right_inverse,
    rw function.left_inverse,
    simp,
  end,
}



lemma xz_2_1_3_r (H : subgroup G) (a b: G) : (right_coset ↑H a ≠ right_coset ↑H b) → right_coset ↑H a ∩ right_coset ↑H b = ∅ :=
begin
  rw ne,
  rw xz_2_1_1_r,
  intro h,
  contrapose! h,
  rw [set.ne_empty_iff_nonempty, set.nonempty_def] at h,
  rcases h with ⟨g, ⟨h1, hg1, hg1'⟩, ⟨h2, hg2, hg2'⟩⟩, simp at *,
  obtain rfl := eq_mul_inv_of_mul_eq hg1', clear hg1',
  obtain rfl := eq_mul_inv_of_mul_eq hg2', clear hg2',
  have := mul_mem (inv_mem hg1) hg2,
  simpa [mul_assoc] using this,
end

-- #check left_coset_equivalence
-- #check left_coset_equivalence_rel
-- #check quotient_group.left_rel
-- #check quotient_group.right_rel
def my_quotient_group_left_rel (H : subgroup G) : setoid G := {
  r := λ x y, x⁻¹ * y ∈ H,
  iseqv:= begin
    simp_rw ←left_coset_eq_iff,
    refine ⟨_,_,_⟩,
    {
      intro x,
      reflexivity,
    },
    {
      intros x y H,
      exact H.symm,
    },
    {
      intros x y z hxy hyz,
      rw hxy,
      rw hyz,
    }
  end,
}

-- variable (H : subgroup G)
-- #check quotient (quotient_group.left_rel H)
-- #check ⟦ quotient_group.left_rel H ⟧
-- #check quotient1

-- #check (quotient_group.left_rel H)
-- #check quot.mk (quotient_group.left_rel H).r
-- #check quotient.mk (1: set H)

-- #check quotient.exists_rep (quot.mk (quotient_group.left_rel H).r)

example (H : subgroup G) : quotient (quotient_group.left_rel H) = (G ⧸ H) :=
begin
  unfold quotient,

  unfold has_quotient.quotient,
  unfold has_quotient.quotient',
  unfold quotient_group.left_rel,
  unfold quotient,
  have := quot.mk (quotient_group.left_rel H).r,
  change quot setoid.r = (G ⧸ H),
  refl,
end

-- #check subgroup.index_mul_card
-- #check  finset
-- lemma index_mul_card [fintype G] (H : subgroup G) [hH : fintype H] :
--   H.index * fintype.card H = fintype.card G :=
-- begin
--   unfold subgroup.index,
--   -- convert_to nat.card (G ⧸ H) * fintype.card ↥H = fintype.card G,
--   have := @nat.card_eq_fintype_card (G ⧸ H),
--   -- unfold subgroup.index has_quotient.quotient has_quotient.quotient' quotient_group.left_rel coe_sort coe_sort has_coe_to_sort.coe nat.card,
--   -- unfold coe_fn has_coe_to_sort.coe cardinal.to_nat,
--   -- simp,
--   sorry,
-- end
#check subgroup.card_eq_card_quotient_mul_card_subgroup

lemma my_subgroup_card_eq_card_quotient_mul_card_subgroup
  [fintype G] (H : subgroup G) [fintype H] [decidable_pred (λ a, a ∈ H)] :
  fintype.card G = fintype.card (G ⧸ H) * fintype.card H :=
begin
  rw ←fintype.card_prod,
  apply fintype.card_congr,
  sorry
end
end chapter2.section2
