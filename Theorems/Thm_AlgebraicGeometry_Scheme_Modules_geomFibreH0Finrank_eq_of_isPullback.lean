import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X A' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom φ)))
    (M : X.Modules) (M' : A'.Modules) (e : (Scheme.Modules.pullback c).obj M ≅ M')
    (K : Type u) [Field K] (sK : S' →+* K) :
    Scheme.Modules.geomFibreH0Finrank f' M' K sK = Scheme.Modules.geomFibreH0Finrank f M K (sK.comp φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.solution
