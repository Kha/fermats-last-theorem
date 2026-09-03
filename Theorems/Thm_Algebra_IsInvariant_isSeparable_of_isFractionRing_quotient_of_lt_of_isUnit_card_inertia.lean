import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise

theorem Algebra.IsInvariant.isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia
    {O : Type} [CommRing O] [IsRegularLocalRing O] (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e)
    (𝔮 : Ideal C) [𝔮.IsPrime] (h𝔮0 : 𝔮 ≠ ⊥) (h𝔮𝔫 : 𝔮 ≤ 𝔫) (h𝔮ne : 𝔮 ≠ 𝔫)
    (𝔰 : Ideal O) [𝔰.IsPrime] [𝔮.LiesOver 𝔰]
    (k ℓ : Type) [Field k] [Field ℓ] [Algebra (O ⧸ 𝔰) k] [IsFractionRing (O ⧸ 𝔰) k]
    [Algebra (C ⧸ 𝔮) ℓ] [IsFractionRing (C ⧸ 𝔮) ℓ] [Algebra k ℓ] [Algebra (O ⧸ 𝔰) ℓ]
    [IsScalarTower (O ⧸ 𝔰) k ℓ] [IsScalarTower (O ⧸ 𝔰) (C ⧸ 𝔮) ℓ] :
    Algebra.IsSeparable k ℓ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia.solution
