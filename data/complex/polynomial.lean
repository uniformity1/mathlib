import analysis.exponential analysis.polynomial
import ring_theory.multiplicity
open complex polynomial finset

set_option eqn_compiler.zeta true

@[elab_as_eliminator] def rec_on_horner {α : Type*}
  [nonzero_comm_ring α] [decidable_eq α]
  {M : polynomial α → Sort*} : Π (p : polynomial α),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (p /ₘ X) < degree p,
  from degree_div_by_monic_lt _ monic_X hp (by rw degree_X; exact dec_trivial),
by rw [← mod_by_monic_add_div p monic_X, mod_by_monic_X, ← coeff_zero_eq_eval_zero,
  add_comm, mul_comm] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : p /ₘ X = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : p /ₘ X = 0
    then show M (p /ₘ X * X), by rw [hpX0, zero_mul]; exact M0
    else MX (p /ₘ X) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] lemma degree_pos_induction_on
  {α : Type*} [nonzero_comm_ring α] [decidable_eq α]
  {P : polynomial α → Prop} (p : polynomial α) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from calc 0 < degree (p + C a) : h0
        ... = degree (C (-a) + (p + C a)) :
          eq.symm $ degree_add_eq_of_degree_lt $
            lt_of_le_of_lt degree_C_le h0
        ... = _ : by simp [is_ring_hom.map_neg (@C α _ _)],
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, not_lt.2 (@lattice.bot_le (  ℕ) _ _)] using h0'))
  h0

open filter

lemma tendsto_at_top_at_top {α β : Type} [preorder α] [preorder β]
  [hα : nonempty α]
  (h : directed (@has_le.le α _) id)
  (f : α → β) :
  tendsto f at_top at_top ↔ ∀ b, ∃ i, ∀ a, i ≤ a → b ≤ f a :=
have directed ge (λ (a : α), principal {b : α | a ≤ b}),
  from λ a b, let ⟨z, hz⟩ := h b a in
    ⟨z, λ s h x hzx, h (le_trans hz.2 hzx),
      λ s h x hzx, h (le_trans hz.1 hzx)⟩,
by rw [tendsto_at_top, at_top, infi_sets_eq this hα]; simp

lemma polynomial_tendsto_infinity {p : polynomial ℂ} (h : 0 < degree p) :
  ∀ x : ℝ, ∃ r > 0, ∀ z : ℂ, r < z.abs → x < (p.eval z).abs :=
degree_pos_induction_on p h
  (λ a ha x, ⟨max (x / a.abs) 1, (lt_max_iff.2 (or.inr zero_lt_one)), λ z hz,
    by simp [(div_lt_iff' (complex.abs_pos.2 ha)).symm, max_lt_iff, *] at *⟩)
  (λ p hp ih x, let ⟨r, hr0, hr⟩ := ih x in
    ⟨max r 1, lt_max_iff.2 (or.inr zero_lt_one), λ z hz, by rw [eval_mul, eval_X, complex.abs_mul];
        exact lt_of_lt_of_le (hr z (lt_of_le_of_lt (le_max_left _ _) hz))
          (le_mul_of_ge_one_right (complex.abs_nonneg _)
            (le_trans (le_max_right _ _) (le_of_lt hz)))⟩)
  (λ p a hp ih x, let ⟨r, hr0, hr⟩ := ih (x + a.abs) in
    ⟨r, hr0, λ z hz, by rw [eval_add, eval_C, ← sub_neg_eq_add];
      exact lt_of_lt_of_le (lt_sub_iff_add_lt.2
        (by rw complex.abs_neg; exact (hr z hz)))
        (le_trans (le_abs_self _) (complex.abs_abs_sub_le_abs_sub _ _))⟩)

noncomputable instance decidable_dvd {α : Type*} [comm_semiring α] [decidable_eq α] :
  decidable_rel (@has_dvd.dvd (polynomial α) _) :=
classical.dec_rel _

lemma polynomial.finite_of_degree_pos {α : Type*} [integral_domain α] [decidable_eq α]
  {p q : polynomial α} (hp : (0 : with_bot ℕ) < degree p) (hq : q ≠ 0) :
  multiplicity.finite p q :=
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn0 : p ^ (nat_degree q + 1) ≠ 0,
    from pow_ne_zero _ hp0,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul_eq hpn0 hr0, nat_degree_pow_eq, add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_ge_one_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

noncomputable def polynomial.multiplicity {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a :  α) : ℕ :=
if h0 : p = 0 then 0 else
(multiplicity (X - C a) p).get (polynomial.finite_of_degree_pos
  (by rw degree_X_sub_C; exact dec_trivial) h0)

lemma pow_multiplicity_dvd {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a : α) :
  (X - C a) ^ polynomial.multiplicity p a ∣ p :=
if h : p = 0 then by simp [h]
else by rw [polynomial.multiplicity, dif_neg h];
  exact multiplicity.spec _

lemma div_by_monic_mul_pow_multiplicity_eq
  {α : Type*} [integral_domain α] [decidable_eq α]
  (p : polynomial α) (a : α) :
  p /ₘ ((X - C a) ^ polynomial.multiplicity p a) *
  (X - C a) ^ polynomial.multiplicity p a = p :=
have monic ((X - C a) ^ polynomial.multiplicity p a),
  from by rw [monic.def, leading_coeff_pow,
    (show _ = _, from monic_X_sub_C _), one_pow],
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_multiplicity_ne_zero
  {α : Type*} [integral_domain α] [decidable_eq α]
  {p : polynomial α} (a : α) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ polynomial.multiplicity p a)).eval a ≠ 0 :=
mt dvd_iff_is_root.2 $ λ ⟨q, hq⟩,
begin
  have := div_by_monic_mul_pow_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    polynomial.multiplicity, dif_neg hp] at this,
  refine multiplicity.is_greatest'
    (polynomial.finite_of_degree_pos
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

local attribute [instance, priority 0] classical.prop_decidable

lemma attains_infi (p : polynomial ℂ) :
  ∃ x, (p.eval x).abs = ⨅ y, (p.eval y).abs :=
if hp0 : 0 < degree p then
have hb : bdd_below (set.range (λ x, (p.eval x).abs)),
  from ⟨0, λ _ ⟨y, hy⟩, (hy : _ = _) ▸ complex.abs_nonneg _⟩,
let ⟨r, hr0, hr⟩ := polynomial_tendsto_infinity hp0 ((⨅ y, (p.eval y).abs) + 1) in
have (⨅ y, (p.eval y).abs) ∈ (λ x, (p.eval x).abs) '' closed_ball 0 r,
  from mem_of_is_glb_of_is_closed
    ⟨λ x ⟨z, hz₁, hz₂⟩, hz₂ ▸ lattice.cinfi_le ⟨0, λ _ ⟨y, hy⟩, (hy : _ = _) ▸ complex.abs_nonneg _⟩,
      λ x hx, lattice.le_cinfi (λ y,
        if hy : y ∈ closed_ball (0 : ℂ) r
        then hx _ ⟨y, hy, rfl⟩
        else have hry : r < y.abs, by simpa [closed_ball, complex.dist_eq] using hy,
          let ⟨z, ⟨g, hg⟩, hz⟩ := lattice.exists_lt_of_cInf_lt
            (show set.range (λ y, (p.eval y).abs) ≠ ∅,
              from set.ne_empty_iff_exists_mem.2 ⟨(p.eval 0).abs, ⟨0, rfl⟩⟩)
            (lt_add_one (⨅ y, (p.eval y).abs)) in
          calc x ≤ z : hx _ ⟨g, classical.by_contradiction $ λ hg0,
              have hrg : r < g.abs, by simpa [closed_ball, complex.dist_eq] using hg0,
              not_le_of_gt hz (hg ▸ (le_of_lt (hr _ hrg))),
            hg⟩
          ... ≤ _ : le_of_lt hz
          ... ≤ _ : le_of_lt (hr _ hry))⟩
    (set.ne_empty_iff_exists_mem.2 ⟨(p.eval 0).abs, ⟨0, by simp [le_of_lt hr0], rfl⟩⟩)
  (closed_of_compact _ (compact_image (proper_space.compact_ball _ _)
    ((polynomial.continuous_eval _).comp complex.continuous_abs))),
let ⟨g, hg⟩ := this in ⟨g, hg.2⟩
else ⟨0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0), eval_C]; simp⟩

noncomputable def nth_root (z : ℂ) (n : ℕ) : ℂ :=
if z = 0 then 0 else exp (log z / n)

lemma exp_mul_nat (z : ℂ) (n : ℕ) : exp (z * n) = exp z ^ n :=
by induction n; simp [*, exp_add, add_mul, mul_add, pow_succ]

@[simp] lemma nth_root_pow (z : ℂ) {n : ℕ} (h : 0 < n) : nth_root z n ^ n = z :=
if hz0 : z = 0 then by simp [hz0, nth_root, zero_pow h]
else by rw [nth_root, if_neg hz0, ← exp_mul_nat, @div_mul_cancel ℂ _ _ _
    (nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 h)), exp_log hz0]

@[simp] lemma nth_root_zero (n : ℕ) : nth_root 0 n = 0 := if_pos rfl

@[simp] lemma nth_root_eq_zero {z : ℂ} {n : ℕ} : nth_root z n = 0 ↔ z = 0 :=
⟨λ h, by_contradiction $ λ hz0, by simpa [nth_root, hz0, exp_ne_zero] using h,
  λ h, h.symm ▸ nth_root_zero n⟩

lemma abs_nth_root (n : ℕ) (z : ℂ) : abs (nth_root z n) =
  real.nth_root (abs z) n :=
if hz0 : z = 0 then by simp [nth_root, real.nth_root, hz0]
else if hn : n = 0 then by simp [hn, real.nth_root, hz0, nth_root]
else have hn : 0 < n, from nat.pos_of_ne_zero hn,
  pow_right_inj (complex.abs_pos.2 (mt nth_root_eq_zero.1 hz0))
    (real.nth_root_pos (mt complex.abs_eq_zero.1 hz0)) hn
    (by rw [← complex.abs_pow, nth_root_pow _ hn, real.nth_root_power
      (complex.abs_pos.2 hz0) hn])

local attribute [instance, priority 0] classical.prop_decidable

lemma exists_root {f : polynomial ℂ} (hf : degree f ≠ 0) : ∃ z : ℂ, is_root f z :=
if hb : degree f = ⊥ then ⟨37, by simp [*, degree_eq_bot] at *⟩
else
have hf : 0 < degree f, by revert hb hf; cases degree f with b;
  [exact dec_trivial, {cases b; exact dec_trivial}],
let ⟨z₀, hz₀⟩ := attains_infi f in
exists.intro z₀ $ by_contradiction $ λ hf0,
have hfX : f - C (f.eval z₀) ≠ 0,
  from mt sub_eq_zero.1 (λ h, not_le_of_gt hf
    (h.symm ▸ degree_C_le)),
let n := polynomial.multiplicity (f - C (f.eval z₀)) z₀ in
let g := (f - C (f.eval z₀)) /ₘ ((X - C z₀) ^ n) in
have hg0 : g.eval z₀ ≠ 0, from eval_div_by_monic_pow_multiplicity_ne_zero _ hfX,
have hg : g * (X - C z₀) ^ n = f - C (f.eval z₀),
  from div_by_monic_mul_pow_multiplicity_eq _ _,
have hn0 : 0 < n, from nat.pos_of_ne_zero $ λ hn0,
  by simpa [g, hn0] using hg0,
let ⟨δ', hδ'₁, hδ'₂⟩ := continuous_of_metric.1 (polynomial.continuous_eval g) z₀
  ((g.eval z₀).abs) (complex.abs_pos.2 hg0) in
let δ := min (min (δ' / 2) 1) (((f.eval z₀).abs / (g.eval z₀).abs) / 2) in
have hf0' : 0 < (f.eval z₀).abs, from complex.abs_pos.2 hf0,
have hfg0 : 0 < abs (eval z₀ f) * (abs (eval z₀ g))⁻¹,
  from div_pos hf0' (complex.abs_pos.2 hg0),
have hδ0 : 0 < δ, from lt_min
  (lt_min (half_pos hδ'₁) (by norm_num)) (half_pos hfg0),
have hδ : ∀ z : ℂ, abs (z - z₀) = δ → abs (g.eval z - g.eval z₀) <
  (g.eval z₀).abs,
  from λ z hz, hδ'₂ z (by rw [complex.dist_eq, hz];
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (half_lt_self hδ'₁)),
have hδ1 : δ ≤ 1, from le_trans (min_le_left _ _) (min_le_right _ _),
let F : polynomial ℂ := C (f.eval z₀) + C (g.eval z₀) * (X - C z₀) ^ n in
let z' := nth_root (-f.eval z₀ * (g.eval z₀).abs * δ ^ n /
  ((f.eval z₀).abs * g.eval z₀)) n + z₀ in
have hF₁ : F.eval z' = f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs,
  by simp [F, nth_root_pow _ hn0, div_eq_mul_inv, eval_pow, mul_assoc,
      mul_comm (g.eval z₀),
      mul_left_comm (g.eval z₀), mul_left_comm (g.eval z₀)⁻¹,
      mul_inv', inv_mul_cancel hg0];
    simp [mul_comm, mul_left_comm, mul_assoc],
have hδs : (g.eval z₀).abs * δ ^ n / (f.eval z₀).abs < 1,
  by rw [div_eq_mul_inv, mul_right_comm, mul_comm,
      ← @inv_inv' _ _ (complex.abs _ * _), mul_inv',
      inv_inv', ← div_eq_mul_inv, div_lt_iff hfg0, one_mul];
    calc δ ^ n ≤ δ ^ 1 : pow_le_pow_of_le_one
        (le_of_lt hδ0) hδ1 hn0
      ... = δ : _root_.pow_one _
      ... ≤ ((f.eval z₀).abs / (g.eval z₀).abs) / 2 : min_le_right _ _
      ... < _ : half_lt_self hfg0,
have hF₂ : (F.eval z').abs = (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n,
  from calc (F.eval z').abs = (f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs).abs : congr_arg abs hF₁
  ... = abs (f.eval z₀) * complex.abs (1 - (g.eval z₀).abs * δ ^ n /
      (f.eval z₀).abs : ℝ) : by rw [← complex.abs_mul];
        exact congr_arg complex.abs
          (by simp [mul_add, add_mul, mul_assoc, div_eq_mul_inv])
  ... = _ : by rw [complex.abs_of_nonneg (sub_nonneg.2 (le_of_lt hδs)),
      mul_sub, mul_div_cancel' _ (ne.symm (ne_of_lt hf0')), mul_one],
have hef0 : abs (eval z₀ g) * (eval z₀ f).abs ≠ 0,
  from mul_ne_zero (mt complex.abs_eq_zero.1 hg0)
    (mt complex.abs_eq_zero.1 hf0),
have hz'z₀ : abs (z' - z₀) = δ,
  by simp [z', mul_assoc, mul_left_comm _ (_ ^ n), mul_comm _ (_ ^ n),
    mul_comm (eval z₀ f).abs, _root_.mul_div_cancel _ hef0, of_real_mul,
    neg_mul_eq_neg_mul_symm, neg_div, abs_nth_root,
    is_absolute_value.abv_pow complex.abs,
    complex.abs_of_nonneg (le_of_lt hδ0), real.nth_root_unique' hδ0 hn0],
have hF₃ : (f.eval z' - F.eval z').abs < (g.eval z₀).abs * δ ^ n,
  from calc (f.eval z' - F.eval z').abs
      = (g.eval z' - g.eval z₀).abs * (z' - z₀).abs ^ n :
        by rw [← eq_sub_iff_add_eq.1 hg, ← is_absolute_value.abv_pow complex.abs,
            ← complex.abs_mul, sub_mul];
          simp [F, eval_pow, eval_add, eval_mul,
            eval_sub, eval_C, eval_X, eval_neg, add_sub_cancel]
  ... = (g.eval z' - g.eval z₀).abs * δ ^ n : by rw hz'z₀
  ... < _ : (mul_lt_mul_right (pow_pos hδ0 _)).2 (hδ _ hz'z₀),
lt_irrefl (f.eval z₀).abs $
calc (f.eval z₀).abs = ⨅ y, (f.eval y).abs : hz₀
... ≤ (f.eval z').abs : lattice.cinfi_le
  ⟨0, λ _ ⟨z, hz⟩, by simp [hz.symm, complex.abs_nonneg]⟩
... = (F.eval z' + (f.eval z' - F.eval z')).abs : by simp
... ≤ (F.eval z').abs + (f.eval z' - F.eval z').abs : complex.abs_add _ _
... < (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n + (g.eval z₀).abs * δ ^ n :
  add_lt_add_of_le_of_lt (by rw hF₂) hF₃
... = (f.eval z₀).abs : sub_add_cancel _ _

lemma irreducible_iff_degree_eq_one {p : polynomial ℂ} : irreducible p ↔ degree p = 1 :=
⟨λ h, le_antisymm
    (le_of_not_gt $ λ hp : 1 < degree p,
      let ⟨z, hz⟩ := exists_root (ne.symm (ne_of_lt (lt_trans dec_trivial hp))) in
      let ⟨b, hb⟩ := dvd_iff_is_root.2 hz in
      have hbu : ¬is_unit b,
        from mt is_unit_iff_degree_eq_zero.1 (λ h, absurd (congr_arg degree hb)
          (λ hd, by rw [degree_mul_eq, h, degree_X_sub_C] at hd;
            rw hd at hp; exact absurd hp dec_trivial)),
      hbu ((h.2 _ b hb).resolve_left (mt is_unit_iff_degree_eq_zero.1
          (by rw [degree_X_sub_C]; exact dec_trivial))))
    (with_bot.add_one_le_iff.2 (degree_pos_of_ne_zero_of_nonunit
      (nonzero_of_irreducible h) h.1)),
  irreducible_of_degree_eq_one⟩