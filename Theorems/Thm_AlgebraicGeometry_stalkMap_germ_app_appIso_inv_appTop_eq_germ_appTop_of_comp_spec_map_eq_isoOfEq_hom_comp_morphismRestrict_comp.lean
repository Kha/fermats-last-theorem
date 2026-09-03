import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
    {X X' : Scheme.{u}} (pr : X' ⟶ X) (U : X.Opens) {Q Q' : Type u} [CommRing Q] [CommRing Q']
    (f : (↑U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q))
    (hWU : pr ⁻¹ᵁ (U.ι ''ᵁ ⊤) = pr ⁻¹ᵁ U)
    (g : (↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}) ⟶ Spec (CommRingCat.of Q')) (ψ : Q →+* Q')
    (hfac : g ≫ Spec.map (CommRingCat.ofHom ψ) = (X'.isoOfEq hWU).hom ≫ (pr ∣_ U) ≫ f)
    (t : Q) (x' : ↥X') (hx' : x' ∈ pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) :
    ((pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)).ι.stalkMap ⟨x', hx'⟩).hom
        ((X'.presheaf.germ (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) x' hx').hom
          ((pr.app (U.ι ''ᵁ ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))))) =
      ((↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}).presheaf.germ ⊤ ⟨x', hx'⟩ trivial).hom
        ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp.solution
