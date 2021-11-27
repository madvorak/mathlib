/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.order.ordered
import analysis.normed_space.order.lattice_ordered_group

/-! # Lattice normed linear ordered group -/

/-- A `lattice_normed_linear_ordered_group` is a `normed_linear_ordered_group` in which
`|x| ≤ |y| → ∥x∥ ≤ ∥y∥`. See also `normed_lattice_add_comm_group`, a related notion in which the
order needs not be linear. -/
class lattice_normed_linear_ordered_group (α : Type*) extends normed_linear_ordered_group α :=
(solid : ∀ x y : α, |x| ≤ |y| → ∥x∥ ≤ ∥y∥)

/-- TODO: is it safe to define this as an instance? -/
def lattice_normed_linear_ordered_group.to_normed_lattice_add_comm_group (E)
  [h : lattice_normed_linear_ordered_group E] :
  normed_lattice_add_comm_group E :=
{ ..h }

noncomputable
instance real.lattice_normed_linear_ordered_group : lattice_normed_linear_ordered_group ℝ :=
{ solid := λ x y h, by rwa [real.norm_eq_abs] }

variables {E : Type*} [lattice_normed_linear_ordered_group E]

lemma norm_le_of_abs_le (x y : E) (h : |x| ≤ |y|) : ∥x∥ ≤ ∥y∥ :=
lattice_normed_linear_ordered_group.solid x y h

lemma norm_max_sub_max_le_norm (x y z : E) : ∥max x z - max y z∥ ≤ ∥x - y∥ :=
norm_le_of_abs_le _ _ (abs_max_sub_max_le_abs x y z)

lemma lipschitz_with_max' : lipschitz_with 1 (λ (x : E), max x 0) :=
lipschitz_with.of_dist_le_mul $ λ x y, by
{ simp only [one_mul, nonneg.coe_one, dist_eq_norm], exact norm_max_sub_max_le_norm x y 0, }
