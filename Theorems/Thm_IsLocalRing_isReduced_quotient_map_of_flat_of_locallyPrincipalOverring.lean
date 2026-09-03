import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring

set_option autoImplicit false

theorem IsLocalRing.isReduced_quotient_map_of_flat_of_locallyPrincipalOverring
    {A B D₁ : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B)
    [CommRing D₁] [IsDomain D₁] [Algebra A D₁] [Module.Finite A D₁]
    (hloc : ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y)
    (𝔭 : Ideal A) (hker : RingHom.ker (algebraMap A D₁) = 𝔭) :
    IsReduced (B ⧸ 𝔭.map (algebraMap A B)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring.solution
