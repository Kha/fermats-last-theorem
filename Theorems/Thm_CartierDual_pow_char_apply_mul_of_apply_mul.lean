import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_pow_char_apply_mul_of_apply_mul

open scoped TensorProduct

universe u v

theorem CartierDual.pow_char_apply_mul_of_apply_mul
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [Bialgebra k B] [Module.Free k B] [Module.Finite k B]
    (δ : CartierDual k B)
    (hδ : ∀ a b : B, δ (a * b) = δ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * δ b)
    (a b : B) :
    (δ ^ p) (a * b) = (δ ^ p) a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * (δ ^ p) b := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_pow_char_apply_mul_of_apply_mul.solution
