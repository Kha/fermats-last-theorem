import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
attribute [-instance] Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem HopfAlgebra.isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
    (p : ℕ) [Fact p.Prime] {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Bc : Type v} [CommRing Bc] [HopfAlgebra (ZMod p) Bc] [Module.Finite (ZMod p) Bc]
    {Be : Type v} [CommRing Be] [HopfAlgebra (ZMod p) Be] [Module.Finite (ZMod p) Be]
    (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
    (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe)
    (hker_πe : RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B)
    (hσ : πe.comp σ = BialgHom.id (ZMod p) Be)
    (hunr : Algebra.FormallyUnramified (ZMod p) Be)
    (hker_qc : RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
      Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)))
    (hΘ : ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
      (Coalgebra.comul (R := ZMod p) b))
    (hBc : IsLocalRing Bc)
    (hord : ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type v) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : B →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M)) :
    IsReduced (CartierDual (ZMod p) Bc) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp.solution
