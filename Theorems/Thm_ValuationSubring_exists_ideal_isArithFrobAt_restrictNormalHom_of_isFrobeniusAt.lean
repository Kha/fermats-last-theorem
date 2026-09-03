import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt

set_option autoImplicit false

open scoped NumberField

theorem ValuationSubring.exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
    {L : Type*} [Field L] [Algebra ℚ L]
    (F : Type*) [Field F] [Algebra ℚ F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L]
    [Normal ℚ F]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    ∃ Q : Ideal (𝓞 F),
      (∀ x : 𝓞 F, x ∈ Q ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits) ∧
      Q.IsMaximal ∧ Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) ∧ Finite (𝓞 F ⧸ Q) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) Q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt.solution
