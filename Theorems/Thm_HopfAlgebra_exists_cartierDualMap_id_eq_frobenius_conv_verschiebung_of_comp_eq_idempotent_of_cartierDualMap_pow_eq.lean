import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] [Module.Free (ZMod p) B]
    (u ε w : B →ₐc[ZMod p] B)
    (hεε : ε.comp ε = ε) (hεu : ε.comp u = u.comp ε)
    (hεw : ε.comp w = w) (hwε : w.comp ε = w)
    (hwuε : w.comp (u.comp ε) = ε) (huεw : (u.comp ε).comp w = ε)
    (hFV : ∀ Fk : B →ₐc[ZMod p] B, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B, (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) B →ₐc[ZMod p] CartierDual (ZMod p) B),
        (CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
              (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) *
            WithConv.toConv ((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B))).ofConv)
    (C : Type) [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C]
    [Module.Finite (ZMod p) C] [Module.Free (ZMod p) C]
    (q : B →ₐc[ZMod p] C) (i : C →ₐc[ZMod p] B)
    (hq : Function.Surjective q) (hqi : q.comp i = BialgHom.id (ZMod p) C) (hiq : i.comp q = ε) :
    ∀ Fk : C →ₐc[ZMod p] C, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) C →ₐ[ZMod p] CartierDual (ZMod p) C, (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (a b : CartierDual (ZMod p) C →ₐc[ZMod p] CartierDual (ZMod p) C),
        (CartierDual.map (BialgHom.id (ZMod p) C) :
            CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) =
          (WithConv.toConv ((FD : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
              (a : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C)) *
            WithConv.toConv ((b : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C))).ofConv := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq.solution
