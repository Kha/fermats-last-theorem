import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_RiemannForm
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [LocallyOfFiniteType f]
    (ι : K ⟶ A) [IsClosedImmersion ι]
    (hfin : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f | ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1}.Finite) :
    IsFinite (ι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq.solution
