import Mathlib
import P2M.Util
import P2M.Sol.S_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange

open scoped TensorProduct

theorem Module.card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange
    (T : Type) [CommRing T] (M : Type) [AddCommGroup M] [Module T M] [Module.Finite ℤ M]
    (𝔪 : Ideal T) (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    Nat.card ↥(Submodule.torsionBySet T (M ⧸ (Ideal.span {((p : ℕ) : T)} • (⊤ : Submodule T M))) 𝔪) =
      p ^ Module.finrank k ↥(⨅ (t : T) (_ : t ∈ 𝔪),
        LinearMap.ker ((DistribSMul.toLinearMap ℤ M t).baseChange k)) := by p2m_exact_reverting @_root_.P2MW.S_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange.solution
