import analysis.exponential topology.instances.polynomial ring_theory.multiplicity
open complex polynomial finset metric

@[simp] lemma coeff_mk {α : Type*} [comm_semiring α] [decidable_eq α] (s) (f) (h) :
  coeff (finsupp.mk s f h : polynomial α) = f := rfl

/-- `dix_X p` return a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X {α : Type*} [comm_semiring α] [decidable_eq α]
  (p : polynomial α) : polynomial α :=
{ to_fun := λ n, p.coeff (n + 1),
  support := ⟨(p.support.filter (> 0)).1.map (λ n, n - 1),
    multiset.nodup_map_on begin
        simp only [finset.mem_def.symm, finset.mem_erase, finset.mem_filter],
        assume x hx y hy hxy,
        rwa [← @add_right_cancel_iff _ _ 1, nat.sub_add_cancel hx.2,
          nat.sub_add_cancel hy.2] at hxy
      end
      (p.support.filter (> 0)).2⟩,
  mem_support_to_fun := λ n,
    suffices (∃ (a : ℕ), (¬coeff p a = 0 ∧ a > 0) ∧ a - 1 = n) ↔
      ¬coeff p (n + 1) = 0,
    by simpa [finset.mem_def.symm, apply_eq_coeff],
    ⟨λ ⟨a, ha⟩, by rw [← ha.2, nat.sub_add_cancel ha.1.2]; exact ha.1.1,
      λ h, ⟨n + 1, ⟨h, nat.succ_pos _⟩, nat.succ_sub_one _⟩⟩ }

lemma div_X_mul_X_add {α : Type*} [comm_semiring α] [decidable_eq α]
  (p : polynomial α) : div_X p * X + C (p.coeff 0) = p :=
polynomial.ext.2 $ λ n,
  nat.cases_on n
   (by simp)
   (by simp [coeff_C, nat.succ_ne_zero, coeff_mul_X, div_X])

@[simp] lemma div_X_C {α : Type*} [comm_semiring α] [decidable_eq α]
  (a : α) : div_X (C a) = 0 :=
polynomial.ext.2 $ λ n, by cases n; simp [div_X, coeff_C]; simp [coeff]

lemma div_X_eq_zero_iff {α : Type*} [comm_semiring α] [decidable_eq α] {p : polynomial α}:
  div_X p = 0 ↔ p = C (p.coeff 0) :=
⟨λ h, by simpa [eq_comm, h] using div_X_mul_X_add p,
  λ h, by rw [h, div_X_C]⟩

lemma div_X_add {α : Type*} [comm_semiring α] [decidable_eq α] {p q: polynomial α}:
  div_X (p + q) = div_X p + div_X q :=
polynomial.ext.2 $ by simp [div_X]

lemma degree_div_X_lt {α : Type*} [comm_semiring α] [decidable_eq α]
  {p : polynomial α} : p ≠ 0 → (div_X p).degree < p.degree :=
polynomial.induction_on p
  (λ a h, have ha : a ≠ 0, by rwa [ne.def, ← C_inj, C_0],
    by rw [div_X_C, degree_zero, degree_C ha]; exact dec_trivial)
  _
  _

@[elab_as_eliminator] def rec_on_horner {α : Type*}
  [comm_semiring α] [decidable_eq α]
  {M : polynomial α → Sort*} : Π (p : polynomial α),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (div_X p) < degree p,
  from degree_div_X_lt hp,
by rw [← div_X_mul_X_add p] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : div_X p = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : div_X p = 0
    then show M (div_X p * X), by rw [hpX0, zero_mul]; exact M0
    else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] lemma degree_pos_induction_on
  {α : Type*} [comm_semiring α] [decidable_eq α]
  {P : polynomial α → Prop} (p : polynomial α) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from lt_of_not_ge (λ h, (not_lt_of_ge degree_C_le) $
        by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0),
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, not_lt.2 (@lattice.bot_le (  ℕ) _ _)] using h0'))
  h0

open filter

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
let n := root_multiplicity z₀ (f - C (f.eval z₀)) in
let g := (f - C (f.eval z₀)) /ₘ ((X - C z₀) ^ n) in
have hg0 : g.eval z₀ ≠ 0, from eval_div_by_monic_pow_root_multiplicity_ne_zero _ hfX,
have hg : g * (X - C z₀) ^ n = f - C (f.eval z₀),
  from div_by_monic_mul_pow_root_multiplicity_eq _ _,
have hn0 : 0 < n, from nat.pos_of_ne_zero $ λ hn0,
  by simpa [g, hn0] using hg0,
let ⟨δ', hδ'₁, hδ'₂⟩ := continuous_iff.1 (polynomial.continuous_eval g) z₀
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
let z' := (-f.eval z₀ * (g.eval z₀).abs * δ ^ n /
  ((f.eval z₀).abs * g.eval z₀)) ^ (n⁻¹ : ℂ) + z₀ in
have hF₁ : F.eval z' = f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs,
  by simp [F, cpow_nat_inv_pow _ hn0, div_eq_mul_inv, eval_pow, mul_assoc,
      mul_comm (g.eval z₀), mul_left_comm (g.eval z₀), mul_left_comm (g.eval z₀)⁻¹,
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
    neg_mul_eq_neg_mul_symm, neg_div, is_absolute_value.abv_pow complex.abs,
    complex.abs_of_nonneg (le_of_lt hδ0), real.pow_nat_rpow_nat_inv (le_of_lt hδ0) hn0],
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
