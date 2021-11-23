import ring_theory.polynomial.cyclotomic
import tactic.by_contra
import topology.algebra.polynomial

lemma is_unit_iff_dvd_units {α} [comm_monoid α] {u : α} : is_unit u ↔ ∀ x, x ∣ u → is_unit x :=
⟨λ hu x hxu, is_unit_of_dvd_unit hxu hu, λ h, h u dvd_rfl⟩

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

namespace polynomial

constant is_root_cyclotomic_iff {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  {μ : R} (hn : (n : R) ≠ 0) : is_primitive_root μ n ↔ is_root (cyclotomic n R) μ

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
  rw [←is_root, ←is_root_cyclotomic_iff] at hy,
  { replace hy := hy.eq_order_of,
    subst hy,
    have := real.order_of_lt y,
    linarith },
  suffices : n ≠ 0, by assumption_mod_cast,
  linarith
end

lemma cyclotomic_pos' {n : ℕ} (h : 2 < n) (x : ℤ) : 0 < eval x (cyclotomic n ℤ) :=
begin
  have := cyclotomic_pos h x,
  rw [←map_cyclotomic_int n ℝ, eval_int_cast_map, int.coe_cast_ring_hom] at this,
  exact_mod_cast this,
end

lemma eval_one_cyclotomic_not_prime_pow {R : Type*} [comm_ring R] {n : ℕ}
  (h : ∀ p : ℕ, p.prime → ∀ k : ℕ, p ^ k ≠ n) : eval 1 (cyclotomic n R) = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  replace hn : 2 < n := sorry,
  suffices : is_unit (eval 1 $ cyclotomic n ℤ), sorry, /-
  { rw [int.is_unit_iff, or_comm] at this,
    cases this with h h,
    { have := cyclotomic_pos' hn 1,
      exfalso,
      linarith },
    have := eval_int_cast_map (int.cast_ring_hom R) (cyclotomic n ℤ) 1,
    simpa only [map_cyclotomic, int.cast_one, h, ring_hom.eq_int_cast] using this },-/
  rw is_unit_iff_dvd_units,
  by_contra' hx,
  obtain ⟨x, hx, hpx⟩ := hx,
  replace hpx : 1 < x.nat_abs,
  { rcases eq_or_ne x 0 with rfl | hx,
    { rw zero_dvd_iff at hx,
      exact ((cyclotomic_pos' hn 1).ne' hx).elim },
    have : ∀ t : ℕ, 1 < t ↔ t ≠ 0 ∧ t ≠ 1,
    { rintro (_|_|t); simp [nat.one_lt_succ_succ] },
    simp [this, hx, (not_iff_not.mpr int.is_unit_iff_nat_abs_eq).mp hpx] },
    let p := x.nat_abs.min_fac,
    have hp : p.prime := nat.min_fac_prime (by linarith),
    replace hx : (p : ℤ) ∣ eval 1 (cyclotomic n ℤ),
    all_goals { sorry },
end

end polynomial
