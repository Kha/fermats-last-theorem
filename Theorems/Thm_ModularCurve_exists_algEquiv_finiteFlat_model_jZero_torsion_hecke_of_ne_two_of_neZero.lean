import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul
open ModularCurve

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφI : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ t))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₀]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₀] [Module.Flat (GaloisRep.ratLocalizedAt p) H₀]
    (e₀ : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he₀_add : ∀ f g, e₀ (f * g) = e₀ f + e₀ g)
    (he₀_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = σ (f h)) → ((e₀ g : JZero N)) = σ • (e₀ f : JZero N))
    (φ₀ : HeckeAlg → (H₀ →ₐ[GaloisRep.ratLocalizedAt p] H₀))
    (hφ₀I : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀)).comap (φ₀ t))
    (hφ₀ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = f (φ₀ t h)) → ((e₀ g : JZero N)) = t • (e₀ f : JZero N)) :
    ∃ ι : H₀ ≃ₐ[GaloisRep.ratLocalizedAt p] H,
      (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H).comp ι.toAlgHom =
        Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀ ∧
      (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f) ∧
      ∀ t : HeckeAlg, ι.toAlgHom.comp (φ₀ t) = (φ t).comp ι.toAlgHom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero.solution
