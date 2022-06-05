import data.setoid.partition
import group_theory.quotient_group

namespace chapter1.section3

variables {α β : Type*} (f : α → β)


-- #check @quotient α (setoid.ker f)
-- #check monoid_hom.ker
-- #check setoid.ker
-- #check set.range
-- #check setoid.quotient_ker_equiv_range


-- #check setoid.quotient_quotient_equiv_quotient

-- 命题 3-1
-- #check setoid.partition.order_iso
-- #check subtype
-- #check setoid.mk_classes

def my_setoid_ker {α : Type*} {β : Type*} (f : α → β) : setoid α := {
  r := λ x y, f x = f y,
  iseqv := begin
    refine ⟨_,_,_⟩,
    {
      intro x,
      refl,
    },
    {
      intros x y h,
      exact h.symm,
    },
    {
      intros x y z hxy hyz,
      rw hxy,
      rw hyz,
    }
  end
}

def function_to_image (f : α → β):  α → {x // x ∈ set.range f} := λ x , ⟨f x, set.mem_range_self x⟩

-- theorem tendsto_def {a : ℕ → ℝ} {t : ℝ} :
--   tendsto a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
-- begin
--   -- true by definition
--   refl
-- end

-- #check @quotient.sound _ (setoid.ker f)
noncomputable def my_quotient_ker_equiv_range : @quotient α (@setoid.ker α β f) ≃ set.range f :=
begin
  refine equiv.of_bijective (λ k , @quotient.lift _ _ (setoid.ker f) (function_to_image f) (λ a b h , subtype.ext_val h) k)  _,
  dunfold function_to_image setoid.ker function.on_fun quotient.lift,
  split,
  {
    intros x y h,
    dsimp at *,
    rcases x,
    rcases y,
    dsimp at h,
    injection h,
    apply quot.sound,
    unfold_projs,
    assumption,
  },
  {
    rintro ⟨y, z, rfl⟩,
    dsimp,
    use @quotient.mk _ (setoid.ker f) z,
    dunfold setoid.ker function.on_fun quotient.mk,
    dsimp,
    refl,
  }
end


-- #check setoid.comap
-- #check setoid.comap_quotient_equiv
noncomputable def my_setoid_comap_quotient_equiv (f : α → β) (r : setoid β) :
  @quotient α (setoid.comap f r) ≃ set.range (@quotient.mk _ r ∘ f) :=
begin
  symmetry,
  apply (setoid.quotient_ker_equiv_range (quotient.mk ∘ f)).symm.trans,
  dunfold setoid.ker function.on_fun function.comp setoid.comap setoid.rel,
  apply quotient.congr_right,
  unfold_projs,
  dsimp,
  intros a b,
  finish,
end

-- #check quot
-- #check setoid.quotient_quotient_equiv_quotient
def my_quotient_quotient_equiv_quotient (r s : setoid α) (h : r ≤ s) :
  quotient (@setoid.ker (@quot α r.rel) (@quot α s.rel) (quot.map_right h)) ≃ @quotient α s :=
  begin
    dunfold has_le.le at h,
    dunfold setoid.ker function.on_fun quot.map_right,
    -- refine ⟨_,_,_,_⟩,
    -- {
    -- }
    sorry,
  end

end chapter1.section3
