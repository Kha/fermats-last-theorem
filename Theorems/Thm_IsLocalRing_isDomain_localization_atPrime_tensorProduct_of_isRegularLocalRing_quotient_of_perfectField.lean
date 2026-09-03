import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem IsLocalRing.isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField
    {A : Type u} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    [PerfectField (IsLocalRing.ResidueField A)]
    (𝒪 : Type u) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [Algebra A 𝒪] [Algebra.EssFiniteType A 𝒪]
    (hϖ : algebraMap A 𝒪 ϖ ∈ IsLocalRing.maximalIdeal 𝒪)
    (hreg : IsRegularLocalRing (𝒪 ⧸ Ideal.span {algebraMap A 𝒪 ϖ}))
    (hdim : ringKrullDim (𝒪 ⧸ Ideal.span {algebraMap A 𝒪 ϖ}) ≤ 1)
    (k : Type u) [Field k] [Algebra A k] (hk : algebraMap A k ϖ = 0)
    (𝔮 : Ideal (𝒪 ⊗[A] k)) [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := 𝒪) (B := k)).toRingHom = IsLocalRing.maximalIdeal 𝒪) :
    IsDomain (Localization.AtPrime 𝔮) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField.solution
