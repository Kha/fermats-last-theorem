import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_MvFormalGroup_finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra instTopologicallyFGOfFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries
attribute [-simp] MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F : MvFormalGroup n k) [F.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F.nthSeries p))) = p ^ h)
    {L : Type v} [CommRing L] [HopfAlgebra k L] [Coalgebra.IsCocomm k L]
    (π : MvPowerSeries (Fin n) k →ₐ[k] L) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span (Set.range (F.nthSeries p)))
    (Θ : MvPowerSeries (Fin n ⊕ Fin n) k →ₐ[k] L ⊗[k] L)
    (hΘl : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = π G ⊗ₜ[k] 1)
    (hΘr : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = 1 ⊗ₜ[k] π G)
    (hcomul : ∀ G, Coalgebra.comul (R := k) (π G) = Θ (MvPowerSeries.subst F.toPowerSeries G))
    (hcounit : ∀ G, Coalgebra.counit (R := k) (π G) = MvPowerSeries.constantCoeff G) :
    Module.finrank k ↥(primitives k L) + n ≤ h := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow.solution
