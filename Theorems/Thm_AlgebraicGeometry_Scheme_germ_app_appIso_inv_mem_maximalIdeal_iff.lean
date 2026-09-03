import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
universe u

theorem AlgebraicGeometry.Scheme.germ_app_appIso_inv_mem_maximalIdeal_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (R : CommRingCat.{u}) (ι : Spec R ⟶ X) [IsOpenImmersion ι]
    (y : ↥Y) (q : PrimeSpectrum ↑R) (hy : f.base y ∈ ι ''ᵁ ⊤) (hq : ι.base q = f.base y) (t : ↑R) :
    (Y.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) y hy).hom
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t))) ∈
      IsLocalRing.maximalIdeal ↑(Y.presheaf.stalk y) ↔ t ∈ q.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff.solution
