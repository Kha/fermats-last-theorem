import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

universe u v

theorem Deformation.DieudonneModule.fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (ℛ₁ : Type v) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    [Module.Flat 𝓞 ↥(HopfAlgebra.hopfKer π)] :
    (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) y = z) ∧
    (∀ y ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
      (∃ x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) →
      ∃ x ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            ↥(HopfAlgebra.hopfKer π) →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ↥(HopfAlgebra.hopfKer π)).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective.solution
