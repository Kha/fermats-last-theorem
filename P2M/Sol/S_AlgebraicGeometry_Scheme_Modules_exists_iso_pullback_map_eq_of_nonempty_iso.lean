import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_eq_of_nonempty_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (N₁ N₂ : A.Modules)
    (hN₂ : Nonempty ((Scheme.Modules.pullback e).obj N₂ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (φ₀ : N₁ ≅ N₂) (ν : (Scheme.Modules.pullback e).obj N₁ ≅ (Scheme.Modules.pullback e).obj N₂) :
    ∃ ψ : N₁ ≅ N₂, (Scheme.Modules.pullback e).map ψ.hom = ν.hom := by
  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial f e he N₂ hN₂
    (((Scheme.Modules.pullback e).mapIso φ₀).symm ≪≫ ν)
  refine ⟨φ₀ ≪≫ θ, ?_⟩
  rw [Iso.trans_hom, Functor.map_comp, hθ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, ← Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
