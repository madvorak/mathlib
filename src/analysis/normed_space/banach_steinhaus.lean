/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.operator_norm
import topology.metric_space.baire
import topology.algebra.module
/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space with is pointwise bounded is uniformly bounded.

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/

variables
{E F 𝕜 𝕜₂ : Type*}
[semi_normed_group E] [semi_normed_group F]
[nondiscrete_normed_field 𝕜] [nondiscrete_normed_field 𝕜₂]
[semi_normed_space 𝕜 E] [semi_normed_space 𝕜₂ F]
{σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]


/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded. -/
theorem banach_steinhaus {ι : Type*} [complete_space E] {g : ι → E →SL[σ₁₂] F}
  ( h : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ∥g i x∥ ≤ C) :
  ∃ C' : ℝ, ∀ i : ι, ∥g i∥ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `∥g i x∥` bounded by `n` -/
  let e : ℕ → set E := λ n, (⋂ i : ι, { x : E | ∥g i x∥ ≤ n }),
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n), from λ i, is_closed_Inter (λ i,
    is_closed_le (continuous.norm (g i).cont) continuous_const),
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = set.univ,
    { apply set.eq_univ_of_forall,
      intro x,
      cases h x with C hC,
      cases (archimedean_iff_nat_le.mp real.archimedean) C with m hm,
      exact ⟨e m, set.mem_range_self m, set.mem_Inter.mpr (λ i, le_trans (hC i) hm)⟩ },
  /- apply the Baire category theorem to conclude `e m` has nonempty interior for some `m : ℕ` -/
  rcases nonempty_interior_of_Union_of_closed hc hU with ⟨m, hm⟩,
  /- extract an `x` and get an `ε`-ball containing it in the interior -/
  rcases set.nonempty_def.mp hm with ⟨x, hx⟩,
  rcases metric.is_open_iff.mp is_open_interior x hx with ⟨ε, ε_pos, hε⟩,
  rcases _inst_3.non_trivial with ⟨(k : 𝕜), hk⟩, -- why didn't it find it?
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ z : E, z ∈ metric.ball x ε → ∀ i : ι, ∥g i z∥ ≤ m,
    { intros z hz i,
      replace hz := set.mem_Inter.mp (interior_Inter_subset _ (hε hz)) i,
      apply interior_subset hz },
  /- show some relevant constants are nonnegative or positive. -/
  have kε_pos : ∥k∥ / ε > 0, from div_pos (lt_trans zero_lt_one hk) (ε_pos),
  have kε_mul_eq_one : (∥k∥ / ε) * (ε / ∥k∥) = 1,
    { rw [div_mul_div, mul_comm, div_eq_one_iff_eq],
      exact ne_of_gt (mul_pos (ε_pos) (lt_trans zero_lt_one hk)) },
  have two_m_nonneg : (2:ℝ) * m ≥ 0, by norm_num,
  have C_pos : (2:ℝ) * m * (∥k∥ / ε) ≥ 0, by nlinarith,
  /- bound norms of `g i`-/
  /- Suppose `y : E` and `ε / ∥k∥ ≤ ∥y∥ < ε`, then for any operator `T` in the collection:
  `∥T y∥ = ∥T (x + y) - T x∥ ≤ ∥T (x + y)∥ + ∥T x∥ ≤ m + m ≤ 2 * m * (∥k∥ / ε) * ∥y∥` -/
  have norm_aux : ∀ i : ι, ∀ y : E, ε / ∥k∥ ≤ ∥y∥ → ∥y∥ < ε → ∥g i y∥ ≤ (2:ℝ) * m * (∥k∥ / ε) * ∥y∥,
    { intros i y le_y y_lt,
      have yx_mem : y + x ∈ metric.ball x ε, by rwa [add_comm, add_mem_ball_iff_norm],
      calc
      ∥g i y∥
          = ∥g i (y + x) - g i x∥   : by simp only [continuous_linear_map.map_add, add_sub_cancel]
      ... ≤ ∥g i (y + x)∥ + ∥g i x∥ : norm_sub_le _ _
      ... ≤ ∥g i (y + x)∥ + m       : by linarith [real_norm_le x (metric.mem_ball_self ε_pos) i]
      ... ≤ 2 * m                   : by linarith [real_norm_le (y + x) yx_mem i]
      ... ≤ (2 * m * (∥k∥ / ε)) * (ε / ∥k∥) : by rw [mul_assoc, kε_mul_eq_one, mul_one]
      ... ≤ (2 * m * (∥k∥ / ε)) * ∥y∥ : by nlinarith [le_y, C_pos] },
  have norm_bd : ∀ i : ι, ∥g i∥ ≤ (2 * m * (∥k∥ / ε)), from
    λ i, continuous_linear_map.op_norm_le_of_shell ε_pos C_pos hk (norm_aux i),
  exact ⟨2 * m * (∥k∥ / ε), norm_bd⟩,
end

open_locale ennreal
open ennreal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `↑∥⬝∥₊ : ℝ≥0∞`
for convenience. -/
theorem banach_steinhaus_supr_nnnorm {ι : Type*} [complete_space E] {g : ι → E →SL[σ₁₂] F}
  ( h : ∀ x : E, (⨆ i : ι, ↑∥g i x∥₊) < ∞) :
  (⨆ i : ι, ↑∥g i∥₊) < ∞ :=
begin
  have h' : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ∥g i x∥ ≤ C,
    { intro x,
      rcases lt_iff_exists_coe.mp (h x) with ⟨p, hp₁, _⟩,
      refine ⟨p, (λ i, _)⟩,
      exact_mod_cast
      calc (∥g i x∥₊ : ℝ≥0∞) ≤ ⨆ j : ι, ∥g j x∥₊ : le_supr _ i
        ...                  = ↑p                : hp₁ },
  cases banach_steinhaus h' with C' hC',
  refine lt_of_le_of_lt (supr_le (λ i, _)) (coe_lt_top),
  { exact C'.to_nnreal },
  { rw ←norm_to_nnreal,
    exact coe_mono (real.to_nnreal_le_to_nnreal (hC' i)) }
end

open_locale topological_space
open filter

/-- Given a *sequence* of continuous linear maps which converges pointwise and for which the
domain is complete, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well. -/
def continuous_linear_map_of_tendsto [complete_space E] [t2_space F]
  {g : ℕ → E →SL[σ₁₂] F} {f : E → F} (h : tendsto (λ n x, g n x) at_top (𝓝 f)) :
  E →SL[σ₁₂] F :=
{ to_fun := f,
  map_add' := (linear_map_of_tendsto h).map_add',
  map_smul' := (linear_map_of_tendsto h).map_smul',
  cont :=
    begin
      /- show that the maps are pointwise bounded and apply `banach_steinhaus`-/
      have h_point_bdd : ∀ x : E, ∃ C : ℝ, ∀ n : ℕ, ∥g n x∥ ≤ C,
        { intro x,
          rcases cauchy_seq_bdd (tendsto_pi_nhds.mp h x).cauchy_seq with ⟨C, C_pos, hC⟩,
          refine ⟨C + ∥g 0 x∥, (λ n, _)⟩,
          simp_rw dist_eq_norm at hC,
          calc ∥g n x∥ ≤ ∥g 0 x∥ + ∥g n x - g 0 x∥ : norm_le_insert' _ _
            ...        ≤ C + ∥g 0 x∥               : by linarith [hC n 0] },
      cases banach_steinhaus h_point_bdd with C' hC',
      /- show the uniform bound from `banach_steinhaus` is the norm bound of the limit map
         by allowing "an `ε` of room." -/
      refine linear_map.continuous_of_bound (linear_map_of_tendsto h) C' _,
      intro x,
      refine _root_.le_of_forall_pos_lt_add (λ ε ε_pos, _),
      cases metric.tendsto_at_top.mp (tendsto_pi_nhds.mp h x) ε ε_pos with n hn,
      have foo'' : ∥g n x - f x∥ < ε, by {rw ←dist_eq_norm, exact hn n (le_refl n)},
      calc ∥f x∥ ≤ ∥g n x∥ + ∥g n x - f x∥ : norm_le_insert _ _
        ...      < ∥g n∥ * ∥x∥ + ε        : by linarith [foo'', (g n).le_op_norm x]
        ...      ≤ C' * ∥x∥ + ε           : by nlinarith [hC' n, norm_nonneg x],
    end }
