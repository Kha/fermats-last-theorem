import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import P2M.Util
import P2M.Sol.S_PadicInt_KummerCarrier_evalAt_bijective_convHom

open scoped TensorProduct in
open PadicInt.KummerCarrier in
theorem PadicInt.KummerCarrier.evalAt_bijective_convHom
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u : ℤ_[p])) :
    ∃ ψ₀ : ZMod p × ZMod p → (Carrier p u →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      Function.Bijective ψ₀ ∧
      (∀ i j : ZMod p, ∃ hw, ψ₀ (i, j) = evalAt p u j (ζ ^ i.val * η ^ j.val) hw) ∧
      ∀ a b : ZMod p × ZMod p,
        (Algebra.TensorProduct.lmul' ℤ_[p] (S := AlgebraicClosure ℚ_[p])).comp
          ((Algebra.TensorProduct.map (ψ₀ a) (ψ₀ b)).comp (Δ p u))
          = ψ₀ (a + b) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_KummerCarrier_evalAt_bijective_convHom.solution
