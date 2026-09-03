import Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.GroupAction.Basic
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt

open NumberField Ideal
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction
theorem FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    MulAction.stabilizer (L ≃ₐ[ℚ] L) Q
      = Subgroup.zpowers (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.solution
