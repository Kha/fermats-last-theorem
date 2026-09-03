import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f] (L : RelativeGroupLaw κ f) (t : ℕ)
    (τ : SchemeHomOver (torusStr κ t) f)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ))
    (T : Type u) [CommRing T] [Algebra κ T] (χ χ' : WithConv (torusCoord κ t →ₐ[κ] T)) :
    NeronModelInfra.schemeHomOverComp (torusPt κ T t (χ * χ').ofConv) τ =
      L.mul _ (NeronModelInfra.schemeHomOverComp (torusPt κ T t χ.ofConv) τ)
        (NeronModelInfra.schemeHomOverComp (torusPt κ T t χ'.ofConv) τ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed.solution
