import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {P : Scheme.{u}}
    (π₁ : P ⟶ Spec (CommRingCat.of R₁)) (π₂ : P ⟶ Spec (CommRingCat.of R₂))
    (N : P.Modules) (𝔚 : P.OrderedAffineCover) :
    ((OModulePresheaf.ofModules π₁ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₁ N).HSucc 𝔚 j)) ↔
      ((OModulePresheaf.ofModules π₂ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₂ N).HSucc 𝔚 j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules.solution
