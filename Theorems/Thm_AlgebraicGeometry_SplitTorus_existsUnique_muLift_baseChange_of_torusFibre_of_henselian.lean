import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus IsLocalRing

theorem AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
    {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R₀ g) (hcomm : L.IsCommutative)
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m))
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField A) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField A) t →ₐ[ResidueField A] ResidueField A),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField A) t χ'.ofConv) τ)) :
    ∃ ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
        NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue A) t m ≫ ι.1 ≫ pullback.fst g σ =
        muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ))) ∧
      ∀ ι' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
        (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι')) →
        (muBaseChange (residue A) t m ≫ ι'.1 ≫ pullback.fst g σ =
          muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)) →
        ι' = ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian.solution
