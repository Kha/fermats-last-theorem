import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus~forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed"

theorem AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
    {κ : Type} [Field κ] [IsAlgClosed κ]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f] (L : RelativeGroupLaw κ f) (t : ℕ)
    (τ τ' : SchemeHomOver (torusStr κ t) f) (hτ : IsClosedImmersion τ.1) (hτ' : IsClosedImmersion τ'.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ))
    (hτ'mul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ'))
    (hrange : Set.range τ'.1.base = Set.range τ.1.base) :
    ∃ Mx : (Fin t → ℤ) ≃+ (Fin t → ℤ),
      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ (Mx : (Fin t → ℤ) →+ (Fin t → ℤ)))) ≫ τ.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq.solution
