import tactic
import group_theory.quotient_group

namespace chapter2.section3

variables {G : Type*} [group G]

-- 定义 3-1 & 命题 3-1 对于正规子群 H 的任意元素 a，其左旁集等于右旁集
lemma definition_3_1 {H : subgroup G} :
  H.normal ↔ ∀ a : G, right_coset ↑H a = left_coset a H :=
⟨
  begin
    intros nH a,
    replace nH := nH.conj_mem,
    ext x,
    unfold right_coset left_coset set.image, simp,
    split; rintro ⟨b,hb, rfl⟩,
    {
      specialize nH _ hb a⁻¹,
      use a⁻¹ * b * a,
      simpa [mul_assoc] using nH,
    },
    {
      specialize nH _ hb a,
      use a * b * a⁻¹,
      simpa [mul_assoc] using nH,
    }
  end,
  λ nH, {
    conj_mem := begin
      dunfold right_coset left_coset set.image at nH,
      intros g hg n,
      specialize nH n,
      rw set.ext_iff at nH,
      simp at nH,
      obtain ⟨g', hg', hh⟩ := (nH (n * g)).mpr ⟨g, hg, rfl⟩,
      convert hg',
      exact mul_inv_eq_of_eq_mul (eq.symm hh),
    end
  }
⟩

-- #check subgroup.centralizer
def my_subgroup_centralizer (H : subgroup G) : subgroup G :=
{
  carrier := H.carrier.centralizer,
  one_mem' := by simp,
  inv_mem' := begin
    simp [set.centralizer],
    intros g h a ha,
    specialize h a ha,
    replace h := eq_mul_inv_of_mul_eq h,
    rw mul_assoc at h,
    replace h := inv_mul_eq_of_eq_mul h,
    exact h.symm,
  end,
  mul_mem' := begin
    simp [set.centralizer],
    intros a b ha hb g hg,
    specialize ha g hg,
    specialize hb g hg,
    clear hg,
    rw ←mul_assoc,
    rw ha,
    rw [mul_assoc, mul_assoc],
    rw ←hb,
  end
}

-- #check subgroup.normalizer
def my_subgroup_normalizer (H : subgroup G) : subgroup G :=
{ carrier := {g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H},
  one_mem' := by simp,
  mul_mem' := begin
    simp,
    intros a b ha hb n,
    convert_to n ∈ H ↔ a * (b * n * b⁻¹) * a⁻¹ ∈ H, { simp [mul_assoc] },
    specialize hb n,
    specialize ha (b * n * b⁻¹),
    rw [hb, ha],
  end,
  inv_mem' := begin
    simp,
    intros a ha n,
    specialize ha (a⁻¹ * n * a⁻¹⁻¹),
    simp [mul_assoc] at *,
    exact ha.symm,
  end
}

def my_subgroup_normalizer2 (H : subgroup G) : subgroup G :=
begin
  have K := my_subgroup_normalizer H,
  refine K.copy {g : G | right_coset ↑H g = left_coset g H} _,
  rw set.ext_iff,
  intro g,
  unfold right_coset left_coset set.image,
  simp,
  rw set.ext_iff,
  simp,
  sorry,
end

-- #check quotient_group.mk

end chapter2.section3
