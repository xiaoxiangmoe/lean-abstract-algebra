import algebra.group.basic

-- 定义 1-1
-- #print semigroup
-- #check @semigroup.mul
-- #check @semigroup.mul_assoc

-- #print monoid
-- #check @monoid.one
-- #check @monoid.one_mul
-- #check @monoid.mul_one

-- 定义 1-2
-- #print group
-- #check @group.inv
-- #check @mul_left_inv
-- #check @mul_right_inv
-- TODO: 交换群，有限群，n 阶群


-- TODO 例子 1-10

namespace dasda

universes u v
variables (σ : Sort u) (τ : Sort v)
#check σ → τ
end dasda

namespace dasda1

universes u v
variables (σ : Sort u) (τ : Sort 0)
#check σ → τ


#print subtype
#check @subtype.mk
#check @subtype.val
#check @subtype.property


end dasda1

namespace dsafas

def foo (h: ∃ n : ℕ, n = n) : ℕ :=
match h with
| Exists.intro n _ := n
end

def foo1 {p q} (h: p ∧ q)  :=
match h with
| and.intro n _ := n
end

#check @foo1
end dsafas
-- variables {G H : Type} [group G] [group H]
namespace chapter2.section1
variables {G : Type*} [group G]
-- 性质 1-1
lemma group_id_uniq (e e': G) :
  (∀ a, e * a = a ∧ a * e = a) ∧ (∀ a, e' * a = a ∧ a * e' = a) → e = e' :=
begin
  rintro ⟨he, he'⟩,
  have h1 := (he e').1,
  have h2 := (he' e).2,
  rw h2 at h1,
  exact h1,
end

-- 性质 1-2
lemma group_inv_uniq (a a₁ a₂: G):
  (a₁ * a = 1 ∧ a * a₁ = 1) ∧ (a₂ * a = 1 ∧ a * a₂ = 1) → a₁ = a₂ :=
begin
  rintro ⟨⟨ha₁l, ha₁r⟩, ⟨ha₂l, ha₂r⟩⟩,
  exact by calc
  a₁  = a₁ * (a * a₂) : by rw [ha₂r, mul_one]
  ... = (a₁ * a) * a₂ : by rw mul_assoc
  ... = a₂ : by rw [ha₁l, one_mul]
end

-- 性质 1-3
lemma my_inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
begin
  have h: a * ((a⁻¹) * (a⁻¹)⁻¹) = a * ((a⁻¹) * a) := begin
    rw mul_inv_self,
    rw inv_mul_self,
  end,
  rw ← mul_assoc at h,
  rw ← mul_assoc at h,
  simp only [mul_inv_self, one_mul] at h,
  exact h,
end
-- 性质 1-4
lemma my_mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  have h: (a * b)⁻¹ * (a * b * (a * b)⁻¹) =  (a * b)⁻¹ * (a * b * (b⁻¹ * a⁻¹)) := by simp,
  rw ← mul_assoc (a * b)⁻¹ (a * b) at h,
  rw ← mul_assoc (a * b)⁻¹ (a * b) at h,
  rw inv_mul_self at h,
  rw one_mul at h,
  rw one_mul at h,
  exact h,
end

-- 性质 1-5

lemma my_mul_inv_rev1 (a b : G) : ∃ x y, a * x = b ∧ y * a = b :=
begin
  use [a⁻¹ * b, b * a⁻¹],
  simp,
end

-- 性质 1-6

lemma my_mul_left_cancel (a b c: G) : a * b = a * c → b = c :=
begin
  intro h,
  convert_to a⁻¹ * a * b = a⁻¹ * a * c,
  { rw inv_mul_self, rw one_mul },
  { rw inv_mul_self, rw one_mul },
  rw mul_assoc,
  rw mul_assoc,
  rw h,
end

-- 略

end chapter2.section1
