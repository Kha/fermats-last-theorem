import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] [Module.Free (ZMod p) B]
    (ε : B →ₐc[ZMod p] B) (hε : ε.comp ε = ε)
    (hFVε : ∀ Fk : B →ₐc[ZMod p] B, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) B →ₐ[ZMod p]
          CartierDual (ZMod p) B, (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (a b : CartierDual (ZMod p) B →ₐc[ZMod p]
          CartierDual (ZMod p) B),
        (CartierDual.map ε :
            CartierDual (ZMod p) B →ₗ[ZMod p]
              CartierDual (ZMod p) B) =
          (WithConv.toConv ((FD : CartierDual (ZMod p) B →ₗ[ZMod p]
                CartierDual (ZMod p) B) ∘ₗ
              (a : CartierDual (ZMod p) B →ₗ[ZMod p]
                CartierDual (ZMod p) B)) *
            WithConv.toConv ((b : CartierDual (ZMod p) B →ₗ[ZMod p]
                CartierDual (ZMod p) B) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) B →ₗ[ZMod p]
                CartierDual (ZMod p) B))).ofConv) :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra (ZMod p) C) (_ : Coalgebra.IsCocomm (ZMod p) C)
      (_ : Module.Finite (ZMod p) C) (_ : Module.Free (ZMod p) C)
      (q : B →ₐc[ZMod p] C) (i : C →ₐc[ZMod p] B),
      Function.Surjective q ∧ q.comp i = BialgHom.id (ZMod p) C ∧ i.comp q = ε ∧
      ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type v) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : C →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung.solution
