/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.basic logic.embedding data.nat.basic

open function

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

structure order_embedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β :=
(ord : ∀ {a b}, r a b ↔ s (to_embedding a) (to_embedding b))

infix ` ≼o `:50 := order_embedding

/-- the induced order on a subtype is an embedding under the natural inclusion. -/
definition subtype.order_embedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
((subtype.val : subtype p → X) ⁻¹'o r) ≼o r :=
⟨⟨subtype.val,subtype.val_injective⟩,by intros;refl⟩

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop}
  (hs : equivalence s) : equivalence (f ⁻¹'o s) :=
⟨λ a, hs.1 _, λ a b h, hs.2.1 h, λ a b c h₁ h₂, hs.2.2 h₁ h₂⟩

namespace order_embedding

instance : has_coe_to_fun (r ≼o s) := ⟨λ _, α → β, λ o, o.to_embedding⟩

theorem ord' : ∀ (f : r ≼o s) {a b}, r a b ↔ s (f a) (f b)
| ⟨f, o⟩ := @o

@[simp] theorem coe_fn_mk (f : α ↪ β) (o) :
  (@order_embedding.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_embedding (f : r ≼o s) : (f.to_embedding : α → β) = f := rfl

theorem eq_of_to_fun_eq : ∀ {e₁ e₂ : r ≼o s}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨⟨f₁, h₁⟩, o₁⟩ ⟨⟨f₂, h₂⟩, o₂⟩ h := by congr; exact h

@[refl] protected def refl (r : α → α → Prop) : r ≼o r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

@[trans] protected def trans (f : r ≼o s) (g : s ≼o t) : r ≼o t :=
⟨f.1.trans g.1, λ a b, by rw [f.2, g.2]; simp⟩

@[simp] theorem refl_apply (x : α) : order_embedding.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≼o s) (g : s ≼o t) (a : α) : (f.trans g) a = g (f a) := rfl

/-- An order embedding is also an order embedding between dual orders. -/
def rsymm (f : r ≼o s) : swap r ≼o swap s :=
⟨f.to_embedding, λ a b, f.ord'⟩

/-- If `f` is injective, then it is an order embedding from the
  preimage order of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ≼o s := ⟨f, λ a b, iff.rfl⟩

theorem eq_preimage (f : r ≼o s) : r = f ⁻¹'o s :=
by funext a b; exact propext f.ord'

protected theorem is_irrefl : ∀ (f : r ≼o s) [is_irrefl β s], is_irrefl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a h, H _ (o.1 h)⟩

protected theorem is_refl : ∀ (f : r ≼o s) [is_refl β s], is_refl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a, o.2 (H _)⟩

protected theorem is_symm : ∀ (f : r ≼o s) [is_symm β s], is_symm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h, o.2 (H _ _ (o.1 h))⟩

protected theorem is_asymm : ∀ (f : r ≼o s) [is_asymm β s], is_asymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (o.1 h₁) (o.1 h₂)⟩

protected theorem is_antisymm : ∀ (f : r ≼o s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_trans : ∀ (f : r ≼o s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.2 (H _ _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_total : ∀ (f : r ≼o s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).2 (H _ _)⟩

protected theorem is_preorder : ∀ (f : r ≼o s) [is_preorder β s], is_preorder α r
| f H := by exactI {..f.is_refl, ..f.is_trans}

protected theorem is_partial_order : ∀ (f : r ≼o s) [is_partial_order β s], is_partial_order α r
| f H := by exactI {..f.is_preorder, ..f.is_antisymm}

protected theorem is_linear_order : ∀ (f : r ≼o s) [is_linear_order β s], is_linear_order α r
| f H := by exactI {..f.is_partial_order, ..f.is_total}

protected theorem is_strict_order : ∀ (f : r ≼o s) [is_strict_order β s], is_strict_order α r
| f H := by exactI {..f.is_irrefl, ..f.is_trans}

protected theorem is_trichotomous : ∀ (f : r ≼o s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff.symm o)).2 (H _ _)⟩

protected theorem is_strict_total_order' : ∀ (f : r ≼o s) [is_strict_total_order' β s], is_strict_total_order' α r
| f H := by exactI {..f.is_trichotomous, ..f.is_strict_order}

protected theorem acc (f : r ≼o s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.ord'.1 h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r ≼o s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected theorem is_well_order : ∀ (f : r ≼o s) [is_well_order β s], is_well_order α r
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order'}

/-- It suffices to prove `f` is monotone between strict orders
  to show it is an order embedding. -/
def of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) : r ≼o s :=
begin
  haveI := @is_irrefl_of_is_asymm β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨H _ _, λ h, _⟩⟩,
  { refine ((@trichotomous _ r _ a b).resolve_left _).resolve_right _;
    exact λ h, @irrefl _ s _ _ (by simpa [e] using H _ _ h) },
  { refine (@trichotomous _ r _ a b).resolve_right (or.rec (λ e, _) (λ h', _)),
    { subst e, exact irrefl _ h },
    { exact asymm (H _ _ h') h } }
end

@[simp] theorem of_monotone_coe [is_trichotomous α r] [is_asymm β s] (f : α → β) (H) :
  (@of_monotone _ _ r s _ _ f H : α → β) = f := rfl

-- If le is preserved by an order embedding of preorders, then lt is too
def lt_embedding_of_le_embedding [preorder α] [preorder β]
  (f : (has_le.le : α → α → Prop) ≼o (has_le.le : β → β → Prop)) :
(has_lt.lt : α → α → Prop) ≼o (has_lt.lt : β → β → Prop) :=
{ to_fun := f,
  inj := f.inj,
  ord := by intros; simp [lt_iff_le_not_le,f.ord] }

theorem nat_lt [is_strict_order α r] (f : ℕ → α) (H : ∀ n:ℕ, r (f n) (f (n+1))) :
  ((<) : ℕ → ℕ → Prop) ≼o r :=
of_monotone f $ λ a b h, begin
  induction b with b IH, {exact (nat.not_lt_zero _ h).elim},
  cases nat.lt_succ_iff_lt_or_eq.1 h with h e,
  { exact trans (IH h) (H _) },
  { subst b, apply H }
end

theorem nat_gt [is_strict_order α r] (f : ℕ → α) (H : ∀ n:ℕ, r (f (n+1)) (f n)) :
  ((>) : ℕ → ℕ → Prop) ≼o r :=
by haveI := is_strict_order.swap r; exact rsymm (nat_lt f H)

theorem well_founded_iff_no_descending_seq [is_strict_order α r] : well_founded r ↔ ¬ nonempty (((>) : ℕ → ℕ → Prop) ≼o r) :=
⟨λ ⟨h⟩ ⟨⟨f, o⟩⟩,
  suffices ∀ a, acc r a → ∀ n, a ≠ f n, from this (f 0) (h _) 0 rfl,
  λ a ac, begin
    induction ac with a _ IH, intros n h, subst a,
    exact IH (f (n+1)) (o.1 (nat.lt_succ_self _)) _ rfl
  end,
λ N, ⟨λ a, classical.by_contradiction $ λ na,
  let ⟨f, h⟩ := classical.axiom_of_choice $
    show ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    from λ ⟨x, h⟩, classical.by_contradiction $ λ hn, h $
      ⟨_, λ y h, classical.by_contradiction $ λ na, hn ⟨⟨y, na⟩, h⟩⟩ in
  N ⟨nat_gt (λ n, (f^[n] ⟨a, na⟩).1) $ λ n,
    by rw nat.iterate_succ'; apply h⟩⟩⟩

end order_embedding

/-- The inclusion map `fin n → ℕ` is an order embedding. -/
def fin.val.order_embedding (n) : @order_embedding (fin n) ℕ (<) (<) :=
⟨⟨fin.val, @fin.eq_of_veq _⟩, λ a b, iff.rfl⟩

/-- The inclusion map `fin m → fin n` is an order embedding. -/
def fin_fin.order_embedding {m n} (h : m ≤ n) : @order_embedding (fin m) (fin n) (<) (<) :=
⟨⟨λ ⟨x, h'⟩, ⟨x, lt_of_lt_of_le h' h⟩,
  λ ⟨a, _⟩ ⟨b, _⟩ h, by congr; injection h⟩,
  by intros; cases a; cases b; refl⟩

instance fin.lt.is_well_order (n) : is_well_order (fin n) (<) :=
(fin.val.order_embedding _).is_well_order

/-- An order isomorphism is an equivalence that is also an order embedding. -/
structure order_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(ord : ∀ {a b}, r a b ↔ s (to_equiv a) (to_equiv b))

infix ` ≃o `:50 := order_iso

namespace order_iso

def to_order_embedding (f : r ≃o s) : r ≼o s :=
⟨f.to_equiv.to_embedding, f.ord⟩

instance : has_coe (r ≃o s) (r ≼o s) := ⟨to_order_embedding⟩

theorem coe_coe_fn (f : r ≃o s) : ((f : r ≼o s) : α → β) = f := rfl

theorem ord' : ∀ (f : r ≃o s) {a b}, r a b ↔ s (f a) (f b)
| ⟨f, o⟩ := @o

@[simp] theorem coe_fn_mk (f : α ≃ β) (o) :
  (@order_iso.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃o s) : (f.to_equiv : α → β) = f := rfl

theorem eq_of_to_fun_eq : ∀ {e₁ e₂ : r ≃o s}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by congr; exact equiv.eq_of_to_fun_eq h

@[refl] protected def refl (r : α → α → Prop) : r ≃o r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

@[symm] protected def symm (f : r ≃o s) : s ≃o r :=
⟨f.to_equiv.symm, λ a b, by cases f with f o; rw o; simp⟩

@[trans] protected def trans (f₁ : r ≃o s) (f₂ : s ≃o t) : r ≃o t :=
⟨f₁.to_equiv.trans f₂.to_equiv, λ a b,
  by cases f₁ with f₁ o₁; cases f₂ with f₂ o₂; rw [o₁, o₂]; simp⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@order_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem refl_apply (x : α) : order_iso.refl r x = x := rfl

@[simp] theorem trans_apply : ∀ (f : r ≃o s) (g : s ≃o t) (a : α), (f.trans g) a = g (f a)
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ a := equiv.trans_apply _ _ _

@[simp] theorem apply_symm_apply : ∀ (e : r ≃o s) (x : β), e (e.symm x) = x
| ⟨f₁, o₁⟩ x := by simp

@[simp] theorem symm_apply_apply : ∀ (e : r ≃o s) (x : α), e.symm (e x) = x
| ⟨f₁, o₁⟩ x := by simp

/-- Any equivalence lifts to an order isomorphism between `s` and its preimage. -/
def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃o s := ⟨f, λ a b, iff.rfl⟩

noncomputable def of_surjective (f : r ≼o s) (H : surjective f) : r ≃o s :=
⟨equiv.of_bijective ⟨f.inj, H⟩, by simp [f.ord']⟩

@[simp] theorem of_surjective_coe (f : r ≼o s) (H) : (of_surjective f H : α → β) = f :=
by delta of_surjective; simp

theorem sum_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @order_iso α₁ α₂ r₁ r₂) (e₂ : @order_iso β₁ β₂ s₁ s₂) :
  sum.lex r₁ s₁ ≃o sum.lex r₂ s₂ :=
⟨equiv.sum_congr e₁.to_equiv e₂.to_equiv, λ a b,
 by cases e₁ with f hf; cases e₂ with g hg;
    cases a; cases b; simp [hf, hg]⟩

theorem prod_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @order_iso α₁ α₂ r₁ r₂) (e₂ : @order_iso β₁ β₂ s₁ s₂) :
  prod.lex r₁ s₁ ≃o prod.lex r₂ s₂ :=
⟨equiv.prod_congr e₁.to_equiv e₂.to_equiv,  λ a b, begin
  cases e₁ with f hf; cases e₂ with g hg,
  cases a with a₁ a₂; cases b with b₁ b₂,
  suffices : prod.lex r₁ s₁ (a₁, a₂) (b₁, b₂) ↔
    prod.lex r₂ s₂ (f a₁, g a₂) (f b₁, g b₂), {simpa [hf, hg]},
  split,
  { intro h, cases h with _ _ _ _ h _ _ _ h,
    { left, exact hf.1 h },
    { right, exact hg.1 h } },
  { generalize e : f b₁ = fb₁,
    intro h, cases h with _ _ _ _ h _ _ _ h,
    { subst e, left, exact hf.2 h },
    { have := f.injective e, subst b₁,
      right, exact hg.2 h } }
end⟩

end order_iso

/-- A subset `p : set α` embeds into `α` -/
def set_coe_embedding {α : Type*} (p : set α) : p ↪ α := ⟨subtype.val, @subtype.eq _ _⟩

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
@subtype.val _ p ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

protected def order_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ≼o r := ⟨set_coe_embedding _, λ a b, iff.rfl⟩

@[simp] theorem order_embedding_apply (r : α → α → Prop) (p a) :
  subrel.order_embedding r p a = a.1 := rfl

instance (r : α → α → Prop) [is_well_order α r]
  (p : set α) : is_well_order p (subrel r p) :=
order_embedding.is_well_order (subrel.order_embedding r p)

end subrel

/-- Restrict the codomain of an order embedding -/
def order_embedding.cod_restrict (p : set β) (f : r ≼o s) (H : ∀ a, f a ∈ p) : r ≼o subrel s p :=
⟨f.to_embedding.cod_restrict p H, f.ord⟩

@[simp] theorem order_embedding.cod_restrict_apply (p) (f : r ≼o s) (H a) :
  order_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl
