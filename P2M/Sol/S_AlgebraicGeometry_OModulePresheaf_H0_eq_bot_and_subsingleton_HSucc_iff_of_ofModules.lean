import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {P : Scheme.{u}}
    (π₁ : P ⟶ Spec (CommRingCat.of R₁)) (π₂ : P ⟶ Spec (CommRingCat.of R₂))
    (N : P.Modules) (𝔚 : P.OrderedAffineCover) :
    ((OModulePresheaf.ofModules π₁ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₁ N).HSucc 𝔚 j)) ↔
      ((OModulePresheaf.ofModules π₂ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₂ N).HSucc 𝔚 j)) := by

  have e : ∀ i : ℕ, (⇑((OModulePresheaf.ofModules π₁ N).d 𝔚 i) : ((OModulePresheaf.ofModules π₁ N).cochain 𝔚 i) → _) =
      ⇑((OModulePresheaf.ofModules π₂ N).d 𝔚 i) := by
    intro i; funext c; funext s
    rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply]
    rfl

  have H0iff : ∀ {R : Type u} [CommRing R] (π : P ⟶ Spec (CommRingCat.of R)),
      (OModulePresheaf.ofModules π N).H0 𝔚 = ⊥ ↔
        ∀ c : (OModulePresheaf.ofModules π N).cochain 𝔚 0, (OModulePresheaf.ofModules π N).d 𝔚 0 c = 0 → c = 0 := by
    intro R _ π
    simp only [OModulePresheaf.H0, Submodule.eq_bot_iff, LinearMap.mem_ker]
  have HSiff : ∀ {R : Type u} [CommRing R] (π : P ⟶ Spec (CommRingCat.of R)) (j : ℕ),
      Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔚 j) ↔
        ∀ c : (OModulePresheaf.ofModules π N).cochain 𝔚 (j + 1), (OModulePresheaf.ofModules π N).d 𝔚 (j + 1) c = 0 →
          ∃ b, (OModulePresheaf.ofModules π N).d 𝔚 j b = c := by
    intro R _ π j
    rw [OModulePresheaf.HSucc, Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
    constructor
    · intro h c hc
      have := h ⟨c, LinearMap.mem_ker.2 hc⟩
      rw [Submodule.mem_comap, LinearMap.mem_range] at this
      exact this
    · rintro h ⟨c, hc⟩
      rw [Submodule.mem_comap, LinearMap.mem_range]
      exact h c (LinearMap.mem_ker.1 hc)
  rw [H0iff π₁, H0iff π₂]
  simp only [HSiff]

  constructor
  · rintro ⟨h0, hS⟩
    refine ⟨fun c hc => h0 c (by rw [e]; exact hc), fun j c hc => ?_⟩
    obtain ⟨b, hb⟩ := hS j c (by rw [e]; exact hc)
    exact ⟨b, by rw [← e]; exact hb⟩
  · rintro ⟨h0, hS⟩
    refine ⟨fun c hc => h0 c (by rw [← e]; exact hc), fun j c hc => ?_⟩
    obtain ⟨b, hb⟩ := hS j c (by rw [← e]; exact hc)
    exact ⟨b, by rw [e]; exact hb⟩
