/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.operator_norm
/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space with is pointwise bounded is uniformly bounded.

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/

open_locale ennreal

variables {E : Type*} {F : Type*} {𝕜 : Type*}
variables [normed_group E] [semi_normed_group F]
variables [nondiscrete_normed_field 𝕜] [semi_normed_space 𝕜 E] [semi_normed_space 𝕜 F]

theorem banach_steinhaus {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
( h : ∀ x : E, (⨆ i : ι, ↑∥g i x∥₊) < ∞) :
(⨆ i : ι, ↑∥g i∥₊) < ∞ :=
sorry
