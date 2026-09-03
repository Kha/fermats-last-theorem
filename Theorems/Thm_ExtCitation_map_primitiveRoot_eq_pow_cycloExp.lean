import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp

namespace ExtCitation
open ValuationSubring
variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
theorem map_primitiveRoot_eq_pow_cycloExp (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) : σ ξ = ξ ^ cycloExp p σ := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp.solution
end ExtCitation
