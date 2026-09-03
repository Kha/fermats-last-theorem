import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp

universe v

theorem HopfAlgebra.exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B] :
    ∃ (n : ℕ) (Hbar : Type v) (_ : CommRing Hbar) (_ : HopfAlgebra (ZMod p) Hbar)
      (_ : Coalgebra.IsCocomm (ZMod p) Hbar) (_ : Module.Finite (ZMod p) Hbar) (_ : IsReduced Hbar)
      (πbar : B →ₐc[ZMod p] Hbar) (jbar : Hbar →ₐc[ZMod p] B),
      Function.Surjective πbar ∧ Function.Injective jbar ∧
      RingHom.ker (πbar : B →ₐ[ZMod p] Hbar) = nilradical B ∧
      ∀ b : B, jbar (πbar b) = b ^ p ^ n := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp.solution
