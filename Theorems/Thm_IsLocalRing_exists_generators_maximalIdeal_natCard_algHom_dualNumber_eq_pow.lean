import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow
    {𝒪 : Type*} {R : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(IsLocalRing.residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    ∃ (m : ℕ) (a : Fin m → R), (∀ i, a i ∈ maximalIdeal R) ∧
      maximalIdeal R ≤ Ideal.span (Set.range a) ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R) ∧
      Nat.card (R →ₐ[𝒪] DualNumber (ResidueField 𝒪)) = Nat.card (ResidueField 𝒪) ^ m := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow.solution
