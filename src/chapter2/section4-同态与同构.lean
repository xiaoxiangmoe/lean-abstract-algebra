import tactic
import group_theory.coset

namespace chapter2.section4


variables {G₁ G₂ G₃ : Type*} [group G₁] [group G₂] [group G₃]

-- 性质 4-1
-- #check map_one
lemma property_4_1__map_one (f: G₁ →* G₂) : f 1 = 1 :=
begin
  have := f.map_mul 1 1,
  rw mul_one at this,
  exact self_eq_mul_left.mp this,
end
-- 性质 4-2
-- #check map_inv
lemma property_4_2__map_inv (f: G₁ →* G₂) (a : G₁) : f a⁻¹ = (f a)⁻¹ :=
begin
  rw ← mul_eq_one_iff_eq_inv,
  rw ← f.map_mul,
  group,
  exact f.map_one,
end

def property_4_3_image (f : G₁ →* G₂) : subgroup G₂ :=
{ carrier := f '' set.univ,
  one_mem' := begin
    simp,
    use 1,
    exact f.map_one
  end,
  mul_mem' := begin
    simp,
    rintro _ _ a rfl b rfl,
    use a * b,
    rw f.map_mul,
  end,
  inv_mem' := begin
    rintro a' ⟨a, -, rfl⟩,
    use a⁻¹,
    exact ⟨set.mem_univ a⁻¹, map_inv f a⟩,
  end,
}
-- pre image or kernel
-- #check monoid_hom.ker
def property_4_4_ker_def (f : G₁ →* G₂) : subgroup G₁ :=
{ carrier := f.mker,
  one_mem' := begin
    -- unfold monoid_hom.mker submonoid.comap submonoid.has_bot monoid_hom.has_coe_to_fun coe lift_t has_lift_t.lift coe_t has_coe_t.coe set_like.coe submonoid.carrier,
    convert_to 1 ∈ ⇑f ⁻¹' {1},
    -- unfold set.preimage has_mem.mem set.mem set_of singleton,
    convert_to f 1 = 1,
    exact f.map_one,
  end,
  mul_mem' := begin
    intros a b,
    convert_to a ∈ ⇑f ⁻¹' {1} → b ∈ ⇑f ⁻¹' {1} → a * b ∈ ⇑f ⁻¹' {1},
    convert_to f a = 1 → f b = 1 → f (a * b) = 1,
    rw map_mul,
    intros ha hb,
    rw [ha, hb],
    exact mul_one 1,
  end,
  inv_mem' := begin
    intro x,
    convert_to x ∈ ⇑f ⁻¹' {1} → x⁻¹ ∈ ⇑f ⁻¹' {1},
    convert_to f x = 1 → f x⁻¹ = 1,
    intro hx,
    rw map_inv,
    rw hx,
    exact inv_one,
  end,
}

-- #check monoid_hom.normal_ker
def property_4_4_monoid_hom_normal_ker (f : G₁ →* G₂) : f.ker.normal :=
{
  conj_mem := begin
    intro x,
    convert_to x ∈ f.mker → ∀ (g : G₁), g * x * g⁻¹ ∈ f.mker,
    -- dunfold monoid_hom.mker submonoid.comap submonoid.has_bot monoid_hom.has_coe_to_fun coe lift_t has_lift_t.lift coe_t has_coe_t.coe set_like.coe submonoid.carrier,
    unfold monoid_hom.mker submonoid.comap,
    simp,
    show f x = 1 → ∀ (g : G₁), f g * f x * (f g)⁻¹ = 1,
    intro h, rw h, clear h x,
    intro g,
    group,
  end
}

-- #check reflexive
def property_4_5_reflexive : G₁ ≃* G₁ :=
{
  to_fun := id,
  inv_fun := id,
  left_inv := by simp [function.left_inverse],
  right_inv := by simp [function.right_inverse, function.left_inverse],
  map_mul' := by simp
}
-- #check symmetric
def property_4_5_symmetric : G₁ ≃* G₂ → G₂ ≃* G₁ := λ hom₁_₂,
{
  to_fun := hom₁_₂.inv_fun,
  inv_fun := hom₁_₂.to_fun,
  left_inv := hom₁_₂.right_inv,
  right_inv := hom₁_₂.left_inv,
  map_mul' := by simp,
}
-- #check transitive
def property_4_5_stransitive : G₁ ≃* G₂ → G₂ ≃* G₃ → G₁ ≃* G₃ := λ hom₁_₂ hom₂_₃,
{
  to_fun := hom₂_₃.to_fun ∘ hom₁_₂.to_fun,
  inv_fun := hom₁_₂.inv_fun ∘ hom₂_₃.inv_fun,
  left_inv := by simp [function.left_inverse],
  right_inv := by simp [function.right_inverse, function.left_inverse],
  map_mul' := by simp,
}


end chapter2.section4
