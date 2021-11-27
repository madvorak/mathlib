/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.lp_space
import analysis.normed_space.lattice_ordered_group

/-!
# Order related properties of Lp spaces

-/

open topological_space measure_theory lattice_ordered_comm_group
open_locale ennreal

variables {α E : Type*} [measurable_space α] {μ : measure α} {p : ℝ≥0∞}
  [normed_lattice_add_comm_group E] [measurable_space E] [borel_space E]
  [second_countable_topology E]

namespace measure_theory

namespace Lp

section order

lemma coe_fn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g :=
by rw [← subtype.coe_le_coe, ← ae_eq_fun.coe_fn_le, ← coe_fn_coe_base, ← coe_fn_coe_base]

lemma coe_fn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f :=
begin
  rw ← Lp.coe_fn_le,
  have h0 := Lp.coe_fn_zero E p μ,
  split; intro h; filter_upwards [h, h0]; intros a h1 h2,
  { rwa h2, },
  { rwa ← h2, },
end

instance : covariant_class (Lp E p μ) (Lp E p μ) has_add.add has_le.le :=
begin
  refine ⟨λ f g₁ g₂ hg₁₂, _⟩,
  rw ← Lp.coe_fn_le at hg₁₂ ⊢,
  have h_add_1 : ⇑(f + g₁) =ᵐ[μ] f + g₁, from Lp.coe_fn_add _ _,
  have h_add_2 : ⇑(f + g₂) =ᵐ[μ] f + g₂, from Lp.coe_fn_add _ _,
  filter_upwards [h_add_1, h_add_2, hg₁₂],
  intros a h1 h2 h3,
  rw [h1, h2, pi.add_apply, pi.add_apply],
  exact add_le_add le_rfl h3,
end

instance : ordered_add_comm_group (Lp E p μ) :=
{ add_le_add_left := λ f g hfg f', add_le_add_left hfg f',
  ..subtype.partial_order _, ..add_subgroup.to_add_comm_group _}

end order

section pos_part

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp E p μ) : Lp E p μ :=
lipschitz_with_pos.comp_Lp (sup_eq_right.mpr (le_refl _)) f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp E p μ) : Lp E p μ := pos_part (-f)

lemma neg_part_eq_pos_part_neg (f : Lp E p μ) : neg_part f = pos_part (-f) := rfl

@[norm_cast]
lemma coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma coe_fn_pos_part (f : Lp E p μ) :
  pos_part f =ᵐ[μ] λ a, (f a) ⊔ 0 :=
by { refine (lipschitz_with.coe_fn_comp_Lp _ _ _).trans _, refl, }

lemma coe_fn_neg_part_eq_max (f : Lp E p μ) :
  neg_part f =ᵐ[μ] λ a, (-f a) ⊔ 0 :=
begin
  rw neg_part,
  refine (coe_fn_pos_part (-f)).trans _,
  refine (coe_fn_neg f).mono (λ a ha, _),
  dsimp only,
  rw ha,
  refl,
end

lemma coe_fn_neg_part (f : Lp E p μ) :
  neg_part f =ᵐ[μ] λ a, - ((f a) ⊓ 0) :=
begin
  refine (coe_fn_neg_part_eq_max f).trans (filter.eventually_of_forall $ λ x, _),
  rw [neg_inf_eq_sup_neg,  neg_zero],
end

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, pos_part f) :=
lipschitz_with.continuous_comp_Lp _ _

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, neg_part f) :=
have eq : (λ f : Lp E p μ, neg_part f) = (λ f : Lp E p μ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

lemma pos_part_eq_zero_iff (f : Lp E p μ) : pos_part f = 0 ↔ f ≤ 0 :=
begin
  rw [← Lp.coe_fn_le, ext_iff],
  have h_pos_part := coe_fn_pos_part f,
  have h0 := coe_fn_zero E p μ,
  split; intro h; filter_upwards [h, h_pos_part, h0]; intros a ha1 ha2 ha3,
  { rw ha1 at ha2,
    rw ha2,
    exact le_sup_left, },
  { rw pi.zero_apply at ha3,
    rw [ha2, ← ha3],
    exact sup_eq_right.mpr ha1, },
end

lemma neg_part_eq_zero_iff (f : Lp E p μ) : neg_part f = 0 ↔ 0 ≤ f :=
by rw [neg_part_eq_pos_part_neg, pos_part_eq_zero_iff, neg_nonpos]

lemma is_closed_nonneg [fact (1 ≤ p)] : is_closed {f : Lp E p μ | 0 ≤ f} :=
begin
  suffices : {f : ↥(Lp E p μ) | 0 ≤ f} = neg_part ⁻¹' {(0 : Lp E p μ)},
  by { rw this, exact is_closed.preimage continuous_neg_part is_closed_singleton, },
  ext1 f,
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_set_of_eq],
  exact (neg_part_eq_zero_iff f).symm,
end

lemma is_closed_le_of_is_closed_nonneg {G} [ordered_add_comm_group G] [topological_space G]
  [has_continuous_sub G]
  (h : is_closed {x : G | 0 ≤ x}) :
  is_closed {p : G × G | p.fst ≤ p.snd} :=
begin
  let F := λ p : G × G, p.snd - p.fst,
  have : {p : G × G | p.fst ≤ p.snd} = F ⁻¹' {x : G | 0 ≤ x},
    by { ext1 p, simp only [sub_nonneg, set.preimage_set_of_eq], },
  rw this,
  exact is_closed.preimage (continuous_snd.sub continuous_fst) h,
end

instance [fact (1 ≤ p)] : order_closed_topology (Lp E p μ) :=
⟨is_closed_le_of_is_closed_nonneg is_closed_nonneg⟩

end pos_part
end Lp
end measure_theory
