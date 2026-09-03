import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

open scoped TensorProduct
open MvPowerSeries

universe v

theorem PDivisibleGroup.exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (G v)) :
    ∃ (d : ℕ) (Φ : MvFormalGroup d (ZMod p)) (_ : Φ.IsComm)
      (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v),
      (∀ v, Function.Surjective (κ v)) ∧
      (∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v)))) ∧
      (∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0) ∧
      (∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
      (∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
          (Φ.toPowerSeries i)) ∧
      Module.finrank (ZMod p)
        (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h ∧
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (G 1)).Cotangent ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (κ v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ F, (∀ v, κ v F = 0) → F = 0) ∧
      (∀ z : ∀ v, G v, (∀ v, s v (z (v + 1)) = z v) → ∃ F, ∀ v, κ v F = z v) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp.solution
