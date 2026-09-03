import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra
  GoodReductionJacobian ModularCurve

theorem ModularCurve.finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    [IsSeparated g] [LocallyOfFiniteType g]
    (proper_away : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Φ : Type) [AddCommGroup Φ] [Finite Φ]
    (comp : ↥(inertiaInvariants A p) →+ Φ)
    (hR1 : ∀ x : ↥(inertiaInvariants A p),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • (x : JZero p) = x) → comp x = 0 →
        ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
          (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1) :
    ((AddSubgroup.closure (Set.range fun s : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) g =>
        pts.symm (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (Category.comp_id _) s))).addSubgroupOf
      (FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p))).FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteIndex_closure_range_sections_addSubgroupOf_fixedPoints_of_compMap.solution
