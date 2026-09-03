import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.map_topToSections_eq_topToSections_topFormMap
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U W : X.Opens} (hWU : W ≤ U) :
    letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
    letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    ∀ [IsScalarTower A Γ(X, U) Γ(X, W)] (η : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))),
      (f.topDifferentials d).presheaf.map (homOfLE hWU).op (f.topToSections d U η) =
        f.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A A Γ(X, U) Γ(X, W) d η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap.solution
