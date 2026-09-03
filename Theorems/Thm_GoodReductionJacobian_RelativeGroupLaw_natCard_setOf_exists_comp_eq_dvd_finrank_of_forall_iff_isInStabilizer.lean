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
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules)
    (ι : K ⟶ A) (hι : IsClosedImmersion ι) (hfin : IsFinite (ι ≫ f))
    (hK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓜 t x) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1} ∣
      (ι ≫ f).finrank (IsLocalRing.closedPoint k) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer.solution
