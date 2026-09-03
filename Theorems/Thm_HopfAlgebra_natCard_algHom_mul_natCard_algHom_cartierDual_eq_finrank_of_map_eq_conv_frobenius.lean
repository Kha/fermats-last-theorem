import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul
set_option autoImplicit false

theorem HopfAlgebra.natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
    (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [HopfAlgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (T : B →ₐc[ZMod q] B) (hT : Function.Bijective T)
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hFV : (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) =
      (WithConv.toConv
          (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) *
        WithConv.toConv
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)).ofConv) :
    Nat.card (B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) *
        Nat.card (CartierDual (ZMod q) B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) B := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.solution
