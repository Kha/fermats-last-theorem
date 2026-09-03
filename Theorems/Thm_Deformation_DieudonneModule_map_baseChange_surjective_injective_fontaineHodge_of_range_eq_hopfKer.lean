import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Deformation.DieudonneModule.map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[𝓞] ℛ)))
    (ℛ₁ : Type v) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (ℛ₃ : Type v) [CommRing ℛ₃] [HopfAlgebra 𝓞 ℛ₃] [Coalgebra.IsCocomm 𝓞 ℛ₃]
    [Module.Free 𝓞 ℛ₃] [Module.Finite 𝓞 ℛ₃]
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    (j : ℛ₃ →ₐc[𝓞] ℛ) (hj : Function.Injective j)
    (hrange : (j : ℛ₃ →ₐ[𝓞] ℛ).range = HopfAlgebra.hopfKer π) :
    Function.Surjective (Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π)) ∧
    Function.Injective (Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j)) ∧
    (∀ x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π)
        (Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) x) = 0) ∧
    (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] (ZMod p) ⊗[𝓞] ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] (ZMod p) ⊗[𝓞] ℛ).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) y = z) ∧
    (∀ x : Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[𝓞] ℛ₃),
      Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) x ∈
        Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] (ZMod p) ⊗[𝓞] ℛ).toRingHom →
      x ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ₃ →ₐ[𝓞] (ZMod p) ⊗[𝓞] ℛ₃).toRingHom) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer.solution
