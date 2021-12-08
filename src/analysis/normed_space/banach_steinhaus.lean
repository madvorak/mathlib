/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.operator_norm
import topology.metric_space.baire
/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space with is pointwise bounded is uniformly bounded.

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/

open_locale ennreal
open ennreal

variables {E : Type*} {F : Type*} {𝕜 : Type*}
variables [normed_group E] [semi_normed_group F]
variables [nondiscrete_normed_field 𝕜] [semi_normed_space 𝕜 E] [semi_normed_space 𝕜 F]

lemma norm_to_nnreal {G : Type*} [semi_normed_group G] {x : G} : ∥x∥.to_nnreal = ∥x∥₊ :=
subtype.ext (eq.trans (real.coe_to_nnreal (∥_∥) (norm_nonneg _)) rfl)

theorem banach_steinhaus {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
( h : ∀ x : E, (⨆ i : ι, ↑∥g i x∥₊) < ∞) :
(⨆ i : ι, ↑∥g i∥₊) < ∞ :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `∥g i x∥` bounded by `n` -/
  let e : ℕ → set E := λ n, (⋂ i : ι, { x : E | (↑∥g i x∥₊ : ℝ≥0∞) ≤ ↑n }),
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n), from λ i, is_closed_Inter (λ i,
    is_closed_le (continuous_coe.comp (continuous.nnnorm (g i).cont)) continuous_const),
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = set.univ,
    { apply set.eq_univ_of_forall,
      intro x,
      rcases lt_iff_exists_coe.mp (h x) with ⟨p,hp₁,_⟩,
      rcases exists_nat_gt p with ⟨m,hm⟩,
      have bound := λ i,
        calc
          (∥g i x∥₊ : ℝ≥0∞) ≤ ⨆ j : ι, ∥g j x∥₊ : le_supr _ i
          ...               = ↑p                : hp₁
          ...               ≤ ↑m                : (coe_lt_coe_nat.mpr hm).le,
      exact ⟨e m, set.mem_range_self m, set.mem_Inter.mpr bound⟩ },
  /- apply the Baire category theorem to conclude `e m` has nonempty interior for some `m : ℕ` -/
  rcases nonempty_interior_of_Union_of_closed hc hU with ⟨m, hm⟩,
  /- extract an `x` and get an `ε`-ball containing it in the interior -/
  rcases set.nonempty_def.mp hm with ⟨x, hx⟩,
  rcases metric.is_open_iff.mp is_open_interior x hx with ⟨ε, ε_pos, hε⟩,
  rcases _inst_3.non_trivial with ⟨(k : 𝕜), hk⟩, -- why didn't it find it?
  /- get back to `ℝ` from `ℝ≥0∞`; this makes the calculation `norm_bound` easier later,
     especially so we can use `continuous_linear_map.op_norm_le_of_shell` -/
  have real_norm_le : ∀ z : E, z ∈ metric.ball x ε → ∀ i : ι, ∥g i z∥ ≤ m,
    { intros z hz i,
      replace hz := set.mem_Inter.mp (interior_Inter_subset _ (hε hz)) i,
      replace hz := interior_subset hz,
      simpa only [coe_to_real, coe_nnnorm, to_real_nat, nat.cast_inj]
        using to_real_mono coe_nat_ne_top hz, },
  /- show some relevant constants are nonnegative or positive. -/
  have kε_pos : ∥k∥ / ε > 0, from div_pos (lt_trans zero_lt_one hk) (ε_pos),
  have kε_mul_eq_one : (∥k∥ / ε) * (ε / ∥k∥) = 1,
    { rw [div_mul_div, mul_comm, div_eq_one_iff_eq],
      exact ne_of_gt (mul_pos (ε_pos) (lt_trans zero_lt_one hk)) },
  have two_m_nonneg : (2:ℝ) * m ≥ 0, by norm_num,
  have C_pos : (2:ℝ) * m * (∥k∥ / ε) ≥ 0, by nlinarith,
  /- bound norms of `g i`-/
  /- Suppose `y : E` and `ε / ∥k∥ ≤ ∥y∥ < ε`, then for any operator `T` in the collection:
  `∥T y∥ = ∥T (x + y) - T x∥ ≤ ∥T (x + y)∥ + ∥T x∥ ≤ m + m ≤ 2 * m * (∥k∥ / ε) * ∥x∥` -/
  have norm_aux : ∀ i : ι, ∀ y : E, ε / ∥k∥ ≤ ∥y∥ → ∥y∥ < ε → ∥g i y∥ ≤ (2:ℝ) * m * (∥k∥ / ε) * ∥y∥,
    { intros i y le_y y_lt,
      have yx_mem : y + x ∈ metric.ball x ε, by rwa [add_comm, add_mem_ball_iff_norm],
      calc
      ∥g i y∥ = ∥g i (y + x) - g i x∥  : by simp only [continuous_linear_map.map_add, add_sub_cancel]
        ...  ≤ ∥g i (y + x)∥ + ∥g i x∥ : norm_sub_le _ _
        ...  ≤ ∥g i (y + x)∥ + m       : by linarith [real_norm_le x (metric.mem_ball_self ε_pos) i]
        ...  ≤ 2 * m                   : by linarith [real_norm_le (y + x) yx_mem i]
        ...  ≤ (2 * m * (∥k∥ / ε)) * (ε / ∥k∥) : by rw [mul_assoc, kε_mul_eq_one, mul_one]
        ...  ≤ (2 * m * (∥k∥ / ε)) * ∥y∥ : by nlinarith [le_y, C_pos] },
  have norm_bd : ∀ i : ι, ∥g i∥ ≤ (2 * m * (∥k∥ / ε)), from
    λ i, continuous_linear_map.op_norm_le_of_shell ε_pos C_pos hk (norm_aux i),
  /- convert norm bounds into supremum bound and finish up -/
  have supr_norm_bd : (⨆ i : ι, (∥g i∥₊ : ℝ≥0∞)) ≤ ↑((2:ℝ) * m * (∥k∥ / ε)).to_nnreal, from
    supr_le (λ i,
      by exact_mod_cast eq.trans_le norm_to_nnreal.symm (real.to_nnreal_mono (norm_bd i))),
  exact lt_of_le_of_lt supr_norm_bd (coe_lt_top),
end
