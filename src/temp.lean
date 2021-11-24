import ring_theory.polynomial.cyclotomic
import tactic.by_contra
import topology.algebra.polynomial
import number_theory.padics.padic_norm

lemma nat.ne_one_iff : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.prime ∧ p ∣ n
| 0 := by simpa using (Exists.intro 2 nat.prime_two) -- we need nat.prime_37 pronto ;b
| 1 := by simp [nat.not_prime_one]
| (n+2) :=
let a := n+2 in
let ha : a ≠ 1 := nat.succ_succ_ne_one n in
begin
  simp only [true_iff, ne.def, not_false_iff, ha],
  exact ⟨a.min_fac, nat.min_fac_prime ha, a.min_fac_dvd⟩,
end

lemma nat.eq_one_iff {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.prime → ¬p ∣ n :=
by simpa using not_iff_not.mpr nat.ne_one_iff

namespace complex

theorem of_real_injective : function.injective (of_real : ℝ → ℂ) :=
λ z w hzw, complex.of_real_inj.mp hzw

end complex

section wtf

lemma one_eq_neg_iff {R} [ring R] [nontrivial R] : ring_char R = 2 ↔ (-1 : R) = 1 :=
begin
  rw ←not_iff_not,
  refine ⟨λ hr h1, _, λ h1 hr, _⟩,
  { rw [eq_comm, ←sub_eq_zero, sub_neg_eq_add] at h1,
    cases (ring_char R).eq_zero_or_pos with hrc hrc,
    { haveI := ring_char.eq_iff.mp hrc,
      haveI := char_p.char_p_to_char_zero R,
      apply @two_ne_zero' R,
      exact_mod_cast h1 },
    rw [show (1 + 1 : R) = (1 + 1 : ℕ), by norm_cast, show 1 + 1 = 2, from rfl] at h1,
    have := nat.le_of_dvd zero_lt_two (ring_char.dvd h1),
    interval_cases (ring_char R),
    { exact char_p.ring_char_ne_one h },
    { exact hr h } },
  { rw [eq_comm, ←sub_eq_zero, sub_neg_eq_add, show (1 + 1 : R) = (1 + 1 : ℕ), by norm_cast] at h1,
    apply h1,
    rw [ring_char.spec R, hr] }
end

instance fact_prime_two := fact.mk nat.prime_two

@[simp] lemma order_of_neg_one {R} [ring R] [nontrivial R] :
  order_of (-1 : R) = if ring_char R = 2 then 1 else 2 :=
begin
  split_ifs,
  { simpa [one_eq_neg_iff] using h },
  apply order_of_eq_prime,
  { simp },
  simpa [one_eq_neg_iff] using h
end

end wtf

namespace int

lemma dvd_iff_nat_abs_dvd (a b : ℤ) : a ∣ b ↔ a.nat_abs ∣ b.nat_abs :=
begin
  refine ⟨λ ⟨k, hk⟩, ⟨k.nat_abs, hk.symm ▸ nat_abs_mul a k⟩, _⟩,
  rintro ⟨k, hk⟩,
  rw [←nat_abs_of_nat k, ←nat_abs_mul, nat_abs_eq_nat_abs_iff, neg_mul_eq_mul_neg] at hk,
  cases hk; exact ⟨_, hk⟩
end

end int

namespace polynomial

section eval

variables {R : Type*} [comm_semiring R] {p q : polynomial R} {x : R}

lemma eval_dvd : p ∣ q → eval x p ∣ eval x q :=
eval₂_dvd _ _

lemma eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → eval x p = 0 → eval x q = 0 :=
eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

end eval

axiom is_root_cyclotomic_iff {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  {μ : R} (hn : (n : R) ≠ 0) : is_root (cyclotomic n R) μ ↔ is_primitive_root μ n

lemma real.order_of_lt : ∀ x : ℝ, order_of x ≤ 2 :=
begin
  by_contra' hx,
  obtain ⟨x, hx⟩ := hx,
  have := (is_primitive_root.order_of x).map_of_injective complex.of_real_injective,
  rw complex.is_primitive_root_iff at this,
  rcases this with ⟨k, -, -, hk⟩,
  apply_fun complex.re at hk,
  -- I finally understand why `simp` can be so slow...
  simp only [complex.exp_re, complex.one_re, bit0_zero, add_zero, mul_one, complex.mul_re, zero_mul, complex.of_real_re,
  complex.bit0_re, sub_zero, complex.one_im, complex.of_real_im, complex.I_im, zero_add, complex.bit0_im, complex.I_re,
  complex.of_real_eq_coe, complex.mul_im, mul_zero, complex.div_im, complex.div_re, one_mul, real.exp_zero, zero_div,
  complex.nat_cast_re, complex.nat_cast_im, complex.norm_sq_apply] at hk,
  -- I don't care about this value, so I don't care about removing the common factor
  have := real.abs_cos_le_one _,
  rw hk at this,
  obtain ht | ht := this.eq_or_lt,
  { rcases (abs_eq $ @zero_le_one ℝ _).mp ht with rfl | rfl; simpa [order_of_one] using hx },
  { apply (pow_lt_one (abs_nonneg x) ht $ show order_of x ≠ 0, by linarith).ne,
    have := pow_order_of_eq_one x,
    apply_fun has_abs.abs at this,
    rwa [abs_pow, abs_one] at this },
  { linarith }
end

lemma cyclotomic_pos {n : ℕ} (h : 2 < n) :
  ∀ x, 0 < eval x (cyclotomic n ℝ) :=
begin
  have h0 := cyclotomic_coeff_zero ℝ h.le,
  rw coeff_zero_eq_eval_zero at h0,
  by_contra' hx,
  obtain ⟨x, hx⟩ := hx,
  have := intermediate_value_univ x 0 (polynomial.continuous $ cyclotomic n ℝ),
  obtain ⟨y, hy⟩ := this (show (0 : ℝ) ∈ set.Icc _ _, by simpa [h0] using hx),
  rw [←is_root, is_root_cyclotomic_iff] at hy,
  replace hy := hy.eq_order_of,
  subst hy,
  have := real.order_of_lt y,
  linarith,
  { suffices : n ≠ 0, by assumption_mod_cast,
    linarith }
end

lemma cyclotomic_pos' {n : ℕ} (h : 2 < n) (x : ℤ) : 0 < eval x (cyclotomic n ℤ) :=
begin
  have := cyclotomic_pos h x,
  rw [←map_cyclotomic_int n ℝ, eval_int_cast_map, int.coe_cast_ring_hom] at this,
  exact_mod_cast this,
end

variables {R : Type*} [comm_ring R] {n : ℕ}

open_locale big_operators

lemma prod_cyclotomic_eq_geom_sum (h : 0 < n) (R) [comm_ring R] [is_domain R] :
  ∏ i in n.divisors \ {1}, cyclotomic i R = geom_sum X n :=
begin
  apply_fun (* cyclotomic 1 R) using mul_left_injective₀ (cyclotomic_ne_zero 1 R),
  have : ∏ i in {1}, cyclotomic i R = cyclotomic 1 R := finset.prod_singleton,
  simp_rw [←this, finset.prod_sdiff $ show {1} ⊆ n.divisors, by simp [h.ne'], this, cyclotomic_one,
           geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]
end

@[simp]
lemma eval_geom_sum {R} [comm_semiring R] {n : ℕ} {x : R} : eval x (geom_sum X n) = geom_sum x n :=
by simp [geom_sum_def, eval_finset_sum]

lemma geom_sum_one (R) [semiring R] (n : ℕ) : geom_sum (1 : R) n = n :=
by simp [geom_sum_def]

lemma range_pow_padic_val_nat_subset_factors {n : ℕ} (p : ℕ) [fact p.prime] (hn : n ≠ 0) :
  (finset.range (padic_val_nat p n + 1)).image (pow p) ⊆ n.divisors :=
begin
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw nat.mem_divisors,
  exact ⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩
end

lemma range_pow_padic_val_nat_subset_factors' {n : ℕ} (p : ℕ) [h : fact p.prime] :
  (finset.range (padic_val_nat p n)).image (λ t, p ^ (t + 1)) ⊆ (n.divisors \ {1}) :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw [finset.mem_sdiff, nat.mem_divisors],
  refine ⟨⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩, _⟩,
  rw [finset.mem_singleton],
  nth_rewrite 1 ←one_pow (k + 1),
  exact (nat.pow_lt_pow_of_lt_left h.1.one_lt (nat.succ_pos k)).ne',
end

lemma eval_one_cyclotomic_not_prime_pow  (h : ∀ {p : ℕ}, p.prime → ∀ k : ℕ, p ^ k ≠ n) :
  eval 1 (cyclotomic n R) = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn',
  { simp },
  have hn : 2 < n,
  { rcases n with (_ | _ | _ | n),
    { exact (lt_irrefl 0 hn').elim },
    { exact (h nat.prime_two 0 rfl).elim },
    { exact (h nat.prime_two 1 rfl).elim },
    simp only [nat.succ_eq_add_one],
    linarith },
  suffices : is_unit (eval 1 $ cyclotomic n ℤ),
  { rw [int.is_unit_iff, or_comm] at this,
    cases this with h h,
    { have := cyclotomic_pos' hn 1,
      exfalso,
      linarith },
    have := eval_int_cast_map (int.cast_ring_hom R) (cyclotomic n ℤ) 1,
    simpa only [map_cyclotomic, int.cast_one, h, ring_hom.eq_int_cast] using this },
  rw [int.is_unit_iff, ←int.nat_abs_eq_nat_abs_iff, int.nat_abs_one, nat.eq_one_iff],
  intros p hp hpe,
  haveI := fact.mk hp,

  have hpn : p ∣ n,
  { apply hpe.trans,
    nth_rewrite 1 ←int.nat_abs_of_nat n,
    rw [←int.dvd_iff_nat_abs_dvd, ←int.nat_cast_eq_coe_nat,
        ←geom_sum_one, ←eval_geom_sum, ←prod_cyclotomic_eq_geom_sum hn'],
    apply eval_dvd,
    apply finset.dvd_prod_of_mem,
    simp only [true_and, nat.mem_divisors, finset.mem_sdiff, dvd_refl, finset.mem_singleton],
    split; linarith },

  have := prod_cyclotomic_eq_geom_sum hn' ℤ,
  apply_fun eval 1 at this,
  rw [eval_geom_sum, geom_sum_one, eval_prod, eq_comm,
      ←finset.prod_sdiff $ range_pow_padic_val_nat_subset_factors' p, finset.prod_image] at this,
  simp_rw [eval_one_cyclotomic_prime_pow, finset.prod_const, finset.card_range, mul_comm] at this,
  rw [←finset.prod_sdiff $ show {n} ⊆ _, from _] at this,
  any_goals {apply_instance},
  swap,
  { simp only [not_exists, true_and, exists_prop, dvd_rfl, finset.mem_image, finset.mem_range,
    finset.mem_singleton, finset.singleton_subset_iff, finset.mem_sdiff, nat.mem_divisors, not_and],
    exact ⟨by split; linarith, λ t _, h hp _⟩ },
  rw [←int.nat_abs_of_nat p, ←int.dvd_iff_nat_abs_dvd] at hpe,
  obtain ⟨t, ht⟩ := hpe,
  rw [finset.prod_singleton, ht, mul_left_comm, mul_comm, ←mul_assoc, mul_assoc] at this,
  simp only [int.nat_cast_eq_coe_nat] at *,
  have : (p ^ (padic_val_nat p n) * p : ℤ) ∣ n := ⟨_, this⟩,
  simp only [←pow_succ', int.dvd_iff_nat_abs_dvd, int.nat_abs_of_nat, int.nat_abs_pow] at this,
  exact pow_succ_padic_val_nat_not_dvd hn' this,
  { rintro x - y - hxy,
    apply nat.succ_injective,
    exact nat.pow_right_injective hp.two_le hxy }
end

end polynomial
