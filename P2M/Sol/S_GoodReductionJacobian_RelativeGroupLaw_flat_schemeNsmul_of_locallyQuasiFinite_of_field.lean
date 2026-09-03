import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open IsLocalRing

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace A]
    (G : RelativeGroupLaw k f) (n : ℕ) [LocallyQuasiFinite (G.schemeNsmul n)] :
    Flat (G.schemeNsmul n) := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI hnoeth : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  haveI : Nonempty A := ⟨x⟩
  haveI hint : IsIntegral A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  algebraize [((G.schemeNsmul n).stalkMap x).hom]
  haveI : IsRegularLocalRing (A.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
  haveI : IsRegularLocalRing (A.presheaf.stalk ((G.schemeNsmul n).base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) ((G.schemeNsmul n).base x)
  haveI : IsNoetherianRing (A.presheaf.stalk x) := inferInstance
  haveI : IsLocalHom (algebraMap
      ↑(A.presheaf.stalk ((G.schemeNsmul n).base x)) ↑(A.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((G.schemeNsmul n).stalkMap x).hom)

  have hfib : ringKrullDim (↑(A.presheaf.stalk x) ⧸
      (maximalIdeal ↑(A.presheaf.stalk ((G.schemeNsmul n).base x))).map
        (algebraMap ↑(A.presheaf.stalk ((G.schemeNsmul n).base x)) ↑(A.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero (G.schemeNsmul n) x

  have hdim : ringKrullDim (A.presheaf.stalk x) =
      ringKrullDim (A.presheaf.stalk ((G.schemeNsmul n).base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
      (f := f) (G.schemeNsmul n) (G.schemeNsmul_over n) x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (A.presheaf.stalk ((G.schemeNsmul n).base x)) (A.presheaf.stalk x) hfib hdim
