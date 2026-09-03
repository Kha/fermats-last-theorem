import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (φ : S →+* S₀)
    {A A₀ : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀))
    (t : A₀ ⟶ A) (ht : IsPullback t f₀ f (Spec.map (CommRingCat.ofHom φ)))
    (M : A.Modules) (M₀ : A₀.Modules) (hiso : Nonempty ((Scheme.Modules.pullback t).obj M ≅ M₀))
    (k : Type u) [Field k] (sk₀ : S₀ →+* k) :
    Scheme.Modules.geomFibreH0Finrank f M k (sk₀.comp φ) = Scheme.Modules.geomFibreH0Finrank f₀ M₀ k sk₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso.solution
