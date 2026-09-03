import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ringHom_heckeAlgebra_residue_eq_map_of_hasIntegralStructure
attribute [-instance] CuspForm.heckeLocal.instIsLocalizationAtPrime CuspForm.heckeLocal.instIsLocalization CuspForm.heckeBaseAlgebra.instAlgebra CuspForm.heckeLocal.instIsLocalRing CuspForm.heckeLocal.instIsNoetherianRing CuspForm.heckeLocal.instCommRing CuspForm.heckeLocalIdeal.instIsMaximal CuspForm.heckeLocal.instIsAdicComplete CuspForm.heckeLatticeAlgebra.instModuleFinite CuspForm.heckeCharKernel.instIsMaximal CuspForm.heckeLocal.instModuleFree CuspForm.heckeBaseAlgebra.instCommRing CuspForm.heckeLocal.instIsScalarTower CuspForm.heckeLatticeAlgebra.instModuleFree CuspForm.heckeLocal.instAlgebra CuspForm.heckeCharKernel.instIsPrime CuspForm.heckeLocal.instModuleFinite CuspForm.heckeLatticeAlgebra.instCommRing CuspForm.heckeLocal.instIsLocalHom CuspForm.heckeLocal.instAlgebraBase GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

theorem CuspForm.exists_ringHom_heckeAlgebra_residue_eq_map_of_hasIntegralStructure
    (N : ℕ) [NeZero N] (S : Set ℕ)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hint : CuspForm.HasIntegralStructure N 2) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∃ χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪',
      ∀ t, IsLocalRing.residue 𝒪' (χ t) = IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ringHom_heckeAlgebra_residue_eq_map_of_hasIntegralStructure.solution
