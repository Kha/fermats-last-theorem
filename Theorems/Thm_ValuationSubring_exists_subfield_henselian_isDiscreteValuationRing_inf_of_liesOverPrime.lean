import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∃ (K₀ : Subfield (AlgebraicClosure ℚ)) (_ : Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ))
      (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : HenselianLocalRing A₀)
      (ι : A₀ →+* ↥A) (_ : IsLocalHom ι) (ϖ₀ : A₀),
      π ∈ K₀ ∧
      Function.Injective ι ∧
      Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
        (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)) ∧
      Function.Surjective ((IsLocalRing.residue ↥A).comp ι) ∧
      maximalIdeal A₀ = Ideal.span {ϖ₀} ∧
      ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime.solution
