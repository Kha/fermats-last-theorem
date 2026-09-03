import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

open scoped TensorProduct

universe v

theorem HopfAlgebra.exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B] :
    ∃ (Bc : Type v) (_ : CommRing Bc) (_ : HopfAlgebra (ZMod p) Bc)
      (_ : Coalgebra.IsCocomm (ZMod p) Bc) (_ : Module.Finite (ZMod p) Bc)
      (Be : Type v) (_ : CommRing Be) (_ : HopfAlgebra (ZMod p) Be)
      (_ : Coalgebra.IsCocomm (ZMod p) Be) (_ : Module.Finite (ZMod p) Be)
      (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
      (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be),
      IsLocalRing Bc ∧ IsReduced Be ∧ Algebra.FormallyUnramified (ZMod p) Be ∧
      Function.Surjective qc ∧ Function.Surjective πe ∧
      RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B ∧
      πe.comp σ = BialgHom.id (ZMod p) Be ∧
      (∀ τ : Be →ₐ[ZMod p] B, (πe : B →ₐ[ZMod p] Be).comp τ = AlgHom.id (ZMod p) Be →
        τ = (σ : Be →ₐ[ZMod p] B)) ∧
      RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
        Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)) ∧
      Function.Bijective Θ ∧
      ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
        (Coalgebra.comul (R := ZMod p) b) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.solution
