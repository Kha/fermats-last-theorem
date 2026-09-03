import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_map_comp_surjective_and_ker_and_fontaineHodge_eq_of_ker_eq_map_ker_counit
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe u

theorem Deformation.HondaSystem.map_comp_surjective_and_ker_and_fontaineHodge_eq_of_ker_eq_map_ker_counit
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Λ : Type u) [CommRing Λ] [HopfAlgebra 𝓞 Λ] [Coalgebra.IsCocomm 𝓞 Λ] [Module.Free 𝓞 Λ]
    [Module.Finite 𝓞 Λ] (hrankΛ : ∃ a : ℕ, Module.finrank 𝓞 Λ = p ^ a)
    (hunipΛ : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) Λ)))
    (Λ' : Type u) [CommRing Λ'] [HopfAlgebra 𝓞 Λ'] [Coalgebra.IsCocomm 𝓞 Λ'] [Module.Free 𝓞 Λ']
    [Module.Finite 𝓞 Λ'] (hrankΛ' : ∃ a : ℕ, Module.finrank 𝓞 Λ' = p ^ a)
    (hunipΛ' : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) Λ')))
    (r v : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (π : (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) Λ))
    (hπs : Function.Surjective π) (hπk : ∀ x, π x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ x, π (H₁.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) Λ) (π x))
    (hπV : ∀ x, π (H₁.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) Λ) (π x))
    (hπL : (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : Λ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Λ).toRingHom).toAddSubgroup =
      H₁.L.toAddSubgroup.map π)
    (π' : (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) Λ'))
    (hπ's : Function.Surjective π')
    (f : Λ' →ₐc[𝓞] Λ) (φ : (Fin r → 𝓞) →ₗ[𝓞] (Fin r → 𝓞))
    (hφv : ∀ x, ∃ y, (p : 𝓞) ^ v • x = φ y)
    (hfφ : ∀ x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) (π' x) = π (φ x))
    (H : Type u) [CommRing H] [HopfAlgebra 𝓞 H] [Coalgebra.IsCocomm 𝓞 H] [Module.Free 𝓞 H]
    [Module.Finite 𝓞 H] (q : Λ →ₐc[𝓞] H) (hq : Function.Surjective q)
    (hexact : RingHom.ker (q : Λ →ₐ[𝓞] H) =
      Ideal.map (f : Λ' →ₐ[𝓞] Λ) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 Λ'))) :
    let ρ : (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) H) :=
      (Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) q)).comp π
    Function.Surjective ρ ∧
      (∀ x, ρ x = 0 ↔ ∃ y, x = φ y) ∧
      (∀ x, ρ (H₁.F x) =
        Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) H) (ρ x)) ∧
      (∀ x, ρ (H₁.V x) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) H) (ρ x)) ∧
      (Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : H →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) H).toRingHom).toAddSubgroup =
        H₁.L.toAddSubgroup.map ρ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_map_comp_surjective_and_ker_and_fontaineHodge_eq_of_ker_eq_map_ker_counit.solution
