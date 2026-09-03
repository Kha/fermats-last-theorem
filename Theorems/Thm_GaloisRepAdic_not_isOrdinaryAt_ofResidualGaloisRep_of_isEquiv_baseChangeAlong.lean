import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_not_isOrdinaryAt_ofResidualGaloisRep_of_isEquiv_baseChangeAlong

theorem GaloisRepAdic.not_isOrdinaryAt_ofResidualGaloisRep_of_isEquiv_baseChangeAlong
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k')
    (ρ₁ : ResidualGaloisRep k) (ρ₂ : ResidualGaloisRep k')
    (he : (ρ₁.baseChangeAlong ψ).IsEquiv ρ₂)
    {p : ℕ} (hp : p.Prime)
    (hnsl : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k' ρ₂.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ₂.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤) :
    ¬ (GaloisRepAdic.ofResidualGaloisRep ρ₁).IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_not_isOrdinaryAt_ofResidualGaloisRep_of_isEquiv_baseChangeAlong.solution
