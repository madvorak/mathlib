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
  /- get back to `ℝ` from `ℝ≥0∞` -/
  have real_norm_le : ∀ z : E, z ∈ metric.ball x ε → ∀ i : ι, ∥g i z∥ ≤ m,
    from sorry,
  /- Suppose `y : E` and `ε / ∥k∥ ≤ ∥y∥ < ε`, then for any operator `T` in the collection:
  `∥T y∥ = ∥T (x + y) - T x∥ ≤ ∥T (x + y)∥ + ∥T x∥ ≤ m + m ≤ 2 * m * (∥k∥ / ε) * ∥x∥` -/
  /- show some relevant constants are nonnegative or positive. -/
  have C_pos : (2:ℝ) * m * (∥k∥ / ε) ≥ 0, from sorry,
  /- bound norms of `g i`-/
  have norm_aux : ∀ i : ι, ∀ y : E, ε / ∥k∥ ≤ ∥y∥ → ∥y∥ < ε → ∥g i y∥ ≤ (2:ℝ) * m * (∥k∥ / ε) * ∥y∥,
    from sorry,
  have norm_bd : ∀ i : ι, ∥g i∥ ≤ (2 * m * (∥k∥ / ε)), from sorry,
  /- convert norm bounds into supremum bound and finish up -/
  have supr_norm_bd : (⨆ i : ι, (∥g i∥₊ : ℝ≥0∞)) ≤ ↑((2:ℝ) * m * (∥k∥ / ε)).to_nnreal,
    from sorry,
  exact lt_of_le_of_lt supr_norm_bd (ennreal.coe_lt_top),
end
