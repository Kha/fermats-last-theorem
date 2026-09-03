import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry open AlgebraicGeometry.Scheme.Modules hiding rightUnitor_hom_app_tensorSections_monoidalV2 associator_hom_app_tensorSections_monoidalV2 tensorHom_app_tensorSections_monoidalV2

theorem AlgebraicGeometry.Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection
    {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(L, U)) (m n : ℕ) :
    (Scheme.Modules.tensorPowAdd L m n).hom.app U
        (Scheme.Modules.tensorSections (L := L.tensorPow m) (M := L.tensorPow n)
          (Scheme.Modules.tensorPowSection g m) (Scheme.Modules.tensorPowSection g n)) =
      Scheme.Modules.tensorPowSection g (m + n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection.solution
