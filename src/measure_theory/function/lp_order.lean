/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.lp_space
import analysis.normed_space.lattice_ordered_group

/-!
# Order related properties of Lp spaces

We show that if `E` is a `normed_lattice_add_comm_group` then so is `Lp E p μ` for `1 ≤ p`.

-/

open topological_space measure_theory lattice_ordered_comm_group
open_locale ennreal

variables {α E : Type*} [measurable_space α] {μ : measure α} {p : ℝ≥0∞}
  [normed_lattice_add_comm_group E] [measurable_space E] [borel_space E]
  [second_countable_topology E]

namespace measure_theory

lemma mem_ℒp.sup {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f ⊔ g) p μ :=
begin
  have h_meas : ae_measurable (f ⊔ g) μ, from hf.1.sup hg.1,
  rw ← mem_ℒp_norm_iff h_meas,
  refine mem_ℒp.of_le (hf.norm.add hg.norm) h_meas.norm _,
  refine filter.eventually_of_forall (λ x, _),
  simp only [pi.sup_apply, pi.add_apply, norm_norm],
  refine (norm_sup_le_add_norm _ _).trans _,
  rw [real.norm_eq_abs, abs_eq_self.mpr (add_nonneg (norm_nonneg _) (norm_nonneg _))],
end

lemma mem_ℒp.inf {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f ⊓ g) p μ :=
begin
  have h_meas : ae_measurable (f ⊓ g) μ, from hf.1.inf hg.1,
  rw ← mem_ℒp_norm_iff h_meas,
  refine mem_ℒp.of_le (hf.norm.add hg.norm) h_meas.norm _,
  refine filter.eventually_of_forall (λ x, _),
  simp only [pi.inf_apply, pi.add_apply, norm_norm],
  refine (norm_inf_le_add_norm _ _).trans _,
  rw [real.norm_eq_abs, abs_eq_self.mpr (add_nonneg (norm_nonneg _) (norm_nonneg _))],
end

lemma mem_Lp_sup {f g : α →ₘ[μ] E} (hf : f ∈ Lp E p μ) (hg : g ∈ Lp E p μ) : f ⊔ g ∈ Lp E p μ :=
begin
  rw Lp.mem_Lp_iff_mem_ℒp at hf hg ⊢,
  rw mem_ℒp_congr_ae (ae_eq_fun.coe_fn_sup _ _),
  exact hf.sup hg,
end

lemma mem_Lp_inf {f g : α →ₘ[μ] E} (hf : f ∈ Lp E p μ) (hg : g ∈ Lp E p μ) : f ⊓ g ∈ Lp E p μ :=
begin
  rw Lp.mem_Lp_iff_mem_ℒp at hf hg ⊢,
  rw mem_ℒp_congr_ae (ae_eq_fun.coe_fn_inf _ _),
  exact hf.inf hg,
end

namespace Lp

section order

lemma coe_fn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g :=
by rw [← subtype.coe_le_coe, ← ae_eq_fun.coe_fn_le, ← coe_fn_coe_base, ← coe_fn_coe_base]

lemma coe_fn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f :=
begin
  rw ← coe_fn_le,
  have h0 := Lp.coe_fn_zero E p μ,
  split; intro h; filter_upwards [h, h0]; intros a h1 h2,
  { rwa h2, },
  { rwa ← h2, },
end

instance : covariant_class (Lp E p μ) (Lp E p μ) has_add.add has_le.le :=
begin
  refine ⟨λ f g₁ g₂ hg₁₂, _⟩,
  rw ← coe_fn_le at hg₁₂ ⊢,
  filter_upwards [coe_fn_add f g₁, coe_fn_add f g₂, hg₁₂],
  intros a h1 h2 h3,
  rw [h1, h2, pi.add_apply, pi.add_apply],
  exact add_le_add le_rfl h3,
end

instance : ordered_add_comm_group (Lp E p μ) :=
{ add_le_add_left := λ f g hfg f', add_le_add_left hfg f',
  ..subtype.partial_order _, ..add_subgroup.to_add_comm_group _}

instance : has_sup (Lp E p μ) := ⟨λ f g, ⟨f.1 ⊔ g.1, mem_Lp_sup f.2 g.2⟩⟩
instance : has_inf (Lp E p μ) := ⟨λ f g, ⟨f.1 ⊓ g.1, mem_Lp_inf f.2 g.2⟩⟩

lemma coe_sup (f g : Lp E p μ) : (↑(f ⊔ g) : α →ₘ[μ] E) = ↑f ⊔ ↑g := rfl
lemma coe_inf (f g : Lp E p μ) : (↑(f ⊓ g) : α →ₘ[μ] E) = ↑f ⊓ ↑g := rfl

lemma coe_fn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] λ a, f a ⊔ g a :=
begin
  rw [coe_fn_coe_base', coe_fn_coe_base', coe_fn_coe_base', coe_sup],
  exact ae_eq_fun.coe_fn_sup _ _,
end

lemma coe_fn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] λ a, f a ⊓ g a :=
begin
  rw [coe_fn_coe_base', coe_fn_coe_base', coe_fn_coe_base', coe_inf],
  exact ae_eq_fun.coe_fn_inf _ _,
end

instance : lattice (Lp E p μ) :=
{ sup := has_sup.sup,
  le_sup_left := λ _ _, @le_sup_left (α →ₘ[μ] E) _ _ _,
  le_sup_right := λ _ _, @le_sup_right (α →ₘ[μ] E) _ _ _,
  sup_le := λ _ _ _, @sup_le (α →ₘ[μ] E) _ _ _ _,
  inf := has_inf.inf,
  inf_le_left := λ _ _, @inf_le_left (α →ₘ[μ] E) _ _ _,
  inf_le_right := λ _ _, @inf_le_right (α →ₘ[μ] E) _ _ _,
  le_inf := λ _ _ _, @le_inf (α →ₘ[μ] E) _ _ _ _,
  ..subtype.partial_order _}

lemma coe_fn_pos (f : Lp E p μ) : ⇑(pos f) =ᵐ[μ] λ a, f a ⊔ 0 :=
begin
  rw lattice_ordered_comm_group.pos,
  filter_upwards [coe_fn_sup f 0, coe_fn_zero E p μ],
  intros a haf ha0,
  rw [haf, ha0, pi.zero_apply],
end

lemma coe_fn_neg_eq_sup_neg (f : Lp E p μ) : ⇑(neg f) =ᵐ[μ] λ a, (-f a) ⊔ 0 :=
begin
  rw lattice_ordered_comm_group.neg,
  filter_upwards [coe_fn_sup (-f) 0, coe_fn_zero E p μ, coe_fn_neg f],
  intros a haf ha0 ha_neg,
  rw [haf, ha_neg, ha0, pi.neg_apply, pi.zero_apply],
end

lemma coe_fn_neg' (f : Lp E p μ) : ⇑(neg f) =ᵐ[μ] λ a, - (f a ⊓ 0) :=
begin
  filter_upwards [coe_fn_neg_eq_sup_neg f],
  intros a ha,
  rw [ha, neg_inf_eq_sup_neg, neg_zero],
end

lemma coe_fn_abs (f : Lp E p μ) : ⇑(|f|) =ᵐ[μ] λ a, |f a| :=
begin
  rw pos_add_neg,
  refine (coe_fn_add _ _).trans _,
  filter_upwards [coe_fn_pos f, coe_fn_neg' f],
  intros a ha_pos ha_neg,
  rw [pi.add_apply, ha_pos, ha_neg, pos_add_neg, lattice_ordered_comm_group.pos,
    lattice_ordered_comm_group.neg, add_right_inj, neg_inf_eq_sup_neg, neg_zero],
end

end order

section pos_part_def

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp E p μ) : Lp E p μ := pos f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp E p μ) : Lp E p μ := neg f

lemma neg_part_eq_pos_part_neg (f : Lp E p μ) : neg_part f = pos_part (-f) := rfl

@[norm_cast]
lemma coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part :=
begin
  ext1,
  rw [← coe_fn_coe_base', pos_part],
  filter_upwards [coe_fn_pos f, ae_eq_fun.coe_fn_pos_part (f : α →ₘ[μ] ℝ)],
  intros a ha1 ha2,
  rw [ha1, ha2, sup_eq_max, coe_fn_coe_base'],
end

lemma pos_part_sub_neg_part (f : Lp E p μ) : pos_part f - neg_part f = f :=
by rw [pos_part, neg_part, ← pos_neg_neg f]

end pos_part_def

section pos_part_prop

@[simp]
lemma pos_part_eq_pos (f : Lp E p μ) : pos_part f = pos f := rfl

@[simp]
lemma neg_part_eq_neg (f : Lp E p μ) : neg_part f = neg f := rfl

lemma pos_part_eq_zero_iff (f : Lp E p μ) : pos_part f = 0 ↔ f ≤ 0 :=
by { rw pos_part_eq_pos, exact pos_eq_zero_iff f, }

lemma neg_part_eq_zero_iff (f : Lp E p μ) : neg_part f = 0 ↔ 0 ≤ f :=
by { rw neg_part_eq_neg, exact neg_eq_zero_iff f, }

end pos_part_prop

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

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, pos_part f) :=
continuous_pos

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λ f : Lp E p μ, neg_part f) :=
continuous_pos_part.comp continuous_neg

end Lp
end measure_theory
