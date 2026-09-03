import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
attribute [-instance] AlgebraicClosure.Rat.isGalois

theorem GaloisRepAdic.isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime) (hdet : ρ.DetIsCyclotomic p)
    (a : A) (ha : a ^ 2 = 1)
    (hline : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule A ρ.V,
        (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
        (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
          ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L)) :
    ρ.IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine.solution
