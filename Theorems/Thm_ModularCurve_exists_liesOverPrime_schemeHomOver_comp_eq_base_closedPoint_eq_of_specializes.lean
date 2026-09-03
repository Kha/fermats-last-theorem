import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

theorem ModularCurve.exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (xη : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X)
    (hxη : xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))
    (x : X) (hPx : xη.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x)
    (hx : ¬ IsUnit ((X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))))) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 = xη ∧
      xA.1.base (IsLocalRing.closedPoint ↥A) = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes.solution
