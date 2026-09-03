import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p]
    (K' : V'.OrderedAffineCover) (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent) :
    (OModulePresheaf.cechPushforward p q K' G).IsQuasicoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.solution
