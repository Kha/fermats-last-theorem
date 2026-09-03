import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

universe v x

theorem Deformation.DieudonneModule.natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
    (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (hA : IsLocalRing (CartierDual (ZMod p) A))
    (Fk : A →ₐc[ZMod p] A) (hFk : ∀ x : A, Fk x = x ^ p)
    (B : Type x) [CommRing B] [Bialgebra (ZMod p) B]
    (q : A →ₐc[ZMod p] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : A →ₐ[ZMod p] B) =
      Ideal.map (Fk : A →ₐ[ZMod p] A) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A))) :
    Nat.card (Deformation.DieudonneModule (ZMod p) p A ⧸
        (Deformation.DieudonneModule.frobenius (ZMod p) p A).range) =
      Nat.card (Deformation.DieudonneModule (ZMod p) p B) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp.solution
