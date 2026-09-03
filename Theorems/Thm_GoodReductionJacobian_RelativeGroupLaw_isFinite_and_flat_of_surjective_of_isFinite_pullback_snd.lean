import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
    {K : Type u} [Field K]
    {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (LX : RelativeGroupLaw K fX)
    (hcX : LX.IsCommutative) (hX : AbelianSchemePropertyBundle K fX)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of K)} (LY : RelativeGroupLaw K fY)
    (hcY : LY.IsCommutative) (hY : AbelianSchemePropertyBundle K fY)
    (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) u =
        LY.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hsurj : Surjective u.1)
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    IsFinite u.1 ∧ Flat u.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.solution
