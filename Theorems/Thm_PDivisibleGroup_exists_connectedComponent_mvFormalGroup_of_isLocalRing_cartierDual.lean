import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_connectedComponent_mvFormalGroup_of_isLocalRing_cartierDual
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem PDivisibleGroup.exists_connectedComponent_mvFormalGroup_of_isLocalRing_cartierDual
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (v : ℕ) :
    ∃ (R₀ : Type v) (_ : CommRing R₀) (_ : HopfAlgebra 𝓞 R₀) (_ : Module.Free 𝓞 R₀)
      (_ : Module.Finite 𝓞 R₀) (ρ : L v →ₐc[𝓞] R₀) (e : L v),
      IsIdempotentElem e ∧ Coalgebra.counit (R := 𝓞) e = 1 ∧
      Function.Surjective ρ ∧ RingHom.ker (ρ : L v →ₐ[𝓞] R₀) = Ideal.span {1 - e} ∧
      IsLocalRing R₀ ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) R₀) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R₀)) ∧
      ∃ (d : ℕ) (F : MvFormalGroup d 𝓞) (_ : F.IsComm) (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀),
        Function.Surjective π ∧
        (∀ i, π (X i) ∈ (Ideal.span {(p : R₀)}).radical) ∧
        (∀ G : MvPowerSeries (Fin d) 𝓞,
          π G = MvFormalGroup.adicEval (Ideal.span {(p : R₀)}) (fun i => π (X i)) G) ∧
        RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))) ∧
        (∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
          MvFormalGroup.adicEval (Ideal.span {(p : R₀ ⊗[𝓞] R₀)})
            (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R₀)) (fun j => (1 : R₀) ⊗ₜ[𝓞] π (X j)))
            (F.toPowerSeries i)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_connectedComponent_mvFormalGroup_of_isLocalRing_cartierDual.solution
