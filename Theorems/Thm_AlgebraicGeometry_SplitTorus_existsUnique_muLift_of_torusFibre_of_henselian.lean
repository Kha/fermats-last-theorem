import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField R) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue R))) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField R) t →ₐ[ResidueField R] ResidueField R),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue R)))).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ'.ofConv) τ))
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m)) :
    ∃ ι : SchemeHomOver (muStr R t m) g,
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue R) t m ≫ ι.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))))) ∧
      ∀ ι' : SchemeHomOver (muStr R t m) g,
        (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι' =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι')
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι')) →
        (muBaseChange (residue R) t m ≫ ι'.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R)))) →
        ι' = ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian.solution
