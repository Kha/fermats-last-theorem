import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_eq_of_nonempty_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_eq_of_nonempty_iso
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (N₁ N₂ : A.Modules)
    (hN₂ : Nonempty ((Scheme.Modules.pullback e).obj N₂ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (φ₀ : N₁ ≅ N₂) (ν : (Scheme.Modules.pullback e).obj N₁ ≅ (Scheme.Modules.pullback e).obj N₂) :
    ∃ ψ : N₁ ≅ N₂, (Scheme.Modules.pullback e).map ψ.hom = ν.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_eq_of_nonempty_iso.solution
