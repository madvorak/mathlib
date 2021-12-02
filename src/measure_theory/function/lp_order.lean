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

lemma coe_fn_pos_part (f : Lp E p μ) : pos_part f =ᵐ[μ] λ a, (f a) ⊔ 0 :=
by { refine (lipschitz_with.coe_fn_comp_Lp _ _ _).trans _, refl, }

lemma coe_fn_neg_part_eq_max (f : Lp E p μ) : neg_part f =ᵐ[μ] λ a, (-f a) ⊔ 0 :=
begin
  rw neg_part,
  refine (coe_fn_pos_part (-f)).trans _,
  refine (coe_fn_neg f).mono (λ a ha, _),
  dsimp only,
  rw ha,
  refl,
end

lemma coe_fn_neg_part (f : Lp E p μ) : neg_part f =ᵐ[μ] λ a, - ((f a) ⊓ 0) :=
begin
  refine (coe_fn_neg_part_eq_max f).trans (filter.eventually_of_forall $ λ x, _),
  rw [neg_inf_eq_sup_neg,  neg_zero],
end

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, pos_part f) :=
lipschitz_with.continuous_comp_Lp _ _

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, neg_part f) :=
continuous_pos_part.comp continuous_neg

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

lemma pos_part_sub_neg_part (f : Lp E p μ) : pos_part f - neg_part f = f :=
begin
  symmetry,
  rw sub_eq_add_neg,
  apply eq_add_neg_of_add_eq,
  rw neg_part_eq_pos_part_neg,
  ext1,
  refine (Lp.coe_fn_add _ _).trans _,
  filter_upwards [coe_fn_pos_part f, coe_fn_pos_part (-f), coe_fn_neg f],
  intros a ha1 ha2 ha3,
  rw [pi.add_apply, ha1, ha2, add_sup_eq_add_sup_add, ha3, pi.neg_apply, add_right_neg, add_zero,
    sup_comm],
end

instance : has_sup (Lp E p μ) :=
{ sup := λ f g, f + pos_part (g - f)}

instance : has_inf (Lp E p μ) :=
{ inf := λ f g, - ((-f) ⊔ (-g)) }

lemma inf_eq_neg_sup_neg (f g : Lp E p μ) : f ⊓ g = - ((-f) ⊔ (-g)) := rfl

lemma sup_eq_left_add (f g : Lp E p μ) : f ⊔ g = f + pos_part (g - f) := rfl

lemma sup_eq_right_add (f g : Lp E p μ) : f ⊔ g = g + pos_part (f - g) :=
by rw [sup_eq_left_add, add_comm, ← sub_eq_sub_iff_add_eq_add,  ← neg_sub g f,
  ← neg_part_eq_pos_part_neg, pos_part_sub_neg_part]

lemma sup_comm (f g : Lp E p μ) : f ⊔ g = g ⊔ f :=
by rw [sup_eq_left_add, sup_eq_right_add]

lemma pos_part_eq_sup_zero (f : Lp E p μ) : pos_part f = f ⊔ 0 :=
by { rw [sup_eq_right_add], simp, }

lemma neg_part_eq_neg_inf_zero (f : Lp E p μ) : neg_part f = -(f ⊓ 0) :=
by { rw [inf_eq_neg_sup_neg, sup_eq_right_add, neg_part], simp, }

lemma pos_part_nonneg (f : Lp E p μ) : 0 ≤ pos_part f :=
begin
  rw ← coe_fn_le,
  filter_upwards [coe_fn_pos_part f, Lp.coe_fn_zero E p μ],
  intros a ha1 ha2,
  rw [ha1, ha2, pi.zero_apply],
  exact le_sup_right,
end

lemma neg_part_nonneg (f : Lp E p μ) : 0 ≤ neg_part f := pos_part_nonneg _

lemma le_sup_left (f g : Lp E p μ) : f ≤ f ⊔ g :=
by { rw sup_eq_left_add, nth_rewrite 0 ← add_zero f, exact add_le_add le_rfl (pos_part_nonneg _), }

lemma le_sup_right (f g : Lp E p μ) : g ≤ f ⊔ g :=
by { rw sup_eq_right_add, nth_rewrite 0 ← add_zero g, exact add_le_add le_rfl (pos_part_nonneg _) }

lemma coe_fn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] λ a, f a ⊔ g a :=
begin
  rw sup_eq_left_add,
  refine (coe_fn_add _ _).trans _,
  filter_upwards [coe_fn_pos_part (g - f), coe_fn_sub g f],
  intros a ha ha_sub,
  rw [pi.add_apply, ha, add_sup_eq_add_sup_add, ha_sub, pi.sub_apply, add_sub_cancel'_right,
    add_zero, _root_.sup_comm],
end

lemma coe_fn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] λ a, f a ⊓ g a :=
begin
  rw inf_eq_neg_sup_neg,
  refine (coe_fn_neg _).trans _,
  filter_upwards [coe_fn_sup (-f) (-g), coe_fn_neg f, coe_fn_neg g],
  intros a ha ha_f ha_g,
  rw [pi.neg_apply, ha, ha_f, ha_g, neg_sup_eq_neg_inf_neg, pi.neg_apply, pi.neg_apply, neg_neg,
    neg_neg],
end

lemma sup_le (f g f' : Lp E p μ) (hff' : f ≤ f') (hgf' : g ≤ f') : f ⊔ g ≤ f' :=
begin
  rw ← coe_fn_le at hff' hgf' ⊢,
  filter_upwards [coe_fn_sup f g, hff', hgf'],
  intros a ha haf hag,
  rw ha,
  exact sup_le haf hag,
end

lemma inf_le_left (f g : Lp E p μ) : f ⊓ g ≤ f :=
by { rw ← coe_fn_le, refine (coe_fn_inf f g).mono (λ a ha, _), rw ha, exact inf_le_left, }

lemma inf_le_right (f g : Lp E p μ) : f ⊓ g ≤ g :=
by { rw ← coe_fn_le, refine (coe_fn_inf f g).mono (λ a ha, _), rw ha, exact inf_le_right, }

lemma le_inf (f' f g : Lp E p μ) (hff' : f' ≤ f) (hgf' : f' ≤ g) : f' ≤ f ⊓ g :=
begin
  rw ← coe_fn_le at hff' hgf' ⊢,
  filter_upwards [coe_fn_inf f g, hff', hgf'],
  intros a ha haf hag,
  rw ha,
  exact le_inf haf hag,
end

instance : lattice (Lp E p μ) :=
{ sup := has_sup.sup,
  le_sup_left := le_sup_left,
  le_sup_right := le_sup_right,
  sup_le := sup_le,
  inf := has_inf.inf,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  ..subtype.partial_order _}

@[simp]
lemma pos_part_eq_pos (f : Lp E p μ) : pos_part f = pos f :=
by { rw lattice_ordered_comm_group.pos, exact pos_part_eq_sup_zero f, }

@[simp]
lemma neg_part_eq_neg (f : Lp E p μ) : neg_part f = neg f :=
by rw [neg_eq_pos_neg, ← pos_part_eq_pos, neg_part]

lemma coe_fn_pos_eq_pos (f : Lp E p μ) : ⇑(pos f) =ᵐ[μ] pos ⇑f :=
begin
  simp_rw lattice_ordered_comm_group.pos,
  filter_upwards [coe_fn_sup f 0, coe_fn_zero E p μ],
  intros a ha ha0,
  rw [ha, ha0],
  simp,
end

lemma coe_fn_neg_eq_neg (f : Lp E p μ) : ⇑(neg f) =ᵐ[μ] neg ⇑f :=
begin
  simp_rw lattice_ordered_comm_group.neg,
  filter_upwards [coe_fn_sup (-f) 0, coe_fn_zero E p μ, coe_fn_neg f],
  intros a ha ha0 ha_neg,
  rw [ha, ha0, ha_neg],
  simp,
end

lemma coe_fn_pos (f : Lp E p μ) : ⇑(pos f) =ᵐ[μ] λ a, (f a) ⊔ 0 :=
by { rw ← pos_part_eq_pos, exact coe_fn_pos_part f, }

lemma coe_fn_neg' (f : Lp E p μ) : ⇑(neg f) =ᵐ[μ] λ a, - ((f a) ⊓ 0) :=
by { rw ← neg_part_eq_neg, exact coe_fn_neg_part f, }

lemma coe_fn_abs (f : Lp E p μ) : ⇑(|f|) =ᵐ[μ] λ a, |f a| :=
begin
  rw pos_add_neg,
  refine (coe_fn_add _ _).trans _,
  filter_upwards [coe_fn_pos f, coe_fn_neg' f],
  intros a ha_pos ha_neg,
  rw [pi.add_apply, ha_pos, ha_neg, pos_add_neg, lattice_ordered_comm_group.pos,
    lattice_ordered_comm_group.neg, add_right_inj, neg_inf_eq_sup_neg, neg_zero],
end

lemma solid (f g : Lp E p μ) (h : |f| ≤ |g|) : ∥f∥ ≤ ∥g∥ :=
begin
  rw ← coe_fn_le at h,
  refine norm_le_norm_of_ae_le _,
  filter_upwards [h, coe_fn_abs f, coe_fn_abs g],
  intros a h_le haf hag,
  rw [haf, hag] at h_le,
  exact solid h_le,
end

noncomputable
instance [fact (1 ≤ p)] : normed_lattice_add_comm_group (Lp E p μ) :=
{ add_le_add_left := λ f g h f', add_le_add_left h _,
  solid := solid, }

end pos_part
end Lp
end measure_theory
