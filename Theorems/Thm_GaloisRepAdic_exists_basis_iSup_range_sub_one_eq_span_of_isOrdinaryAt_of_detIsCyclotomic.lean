import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic

theorem GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic k) (hdet : ρ.DetIsCyclotomic p) (hord : ρ.IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ b : Module.Basis (Fin 2) k ρ.V,
      (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) = k ∙ b 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → ρ.ρ σ (b 0) = (a : k) • b 0 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic.solution
