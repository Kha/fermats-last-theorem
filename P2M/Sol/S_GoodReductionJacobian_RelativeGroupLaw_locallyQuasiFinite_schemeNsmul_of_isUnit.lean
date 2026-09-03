import Mathlib
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [Field R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType f] (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    LocallyQuasiFinite (G.schemeNsmul n) := by
  haveI : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero G hcomm n
      (fun R' S' φ hφ hker t k hk hnk =>
        GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
          G n hn R' S' φ hφ hker t k hk hnk)
  haveI : LocallyOfFiniteType (G.schemeNsmul n) := by
    haveI h : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact AlgebraicGeometry.locallyOfFiniteType_of_comp (G.schemeNsmul n) f
  exact AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
