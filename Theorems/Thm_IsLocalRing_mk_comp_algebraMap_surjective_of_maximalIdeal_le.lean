import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import P2M.Util
import P2M.Sol.S_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le

universe u v
theorem IsLocalRing.mk_comp_algebraMap_surjective_of_maximalIdeal_le
    {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A]
    (hres : Function.Surjective (⇑(IsLocalRing.residue A) ∘ ⇑(algebraMap 𝒪 A)))
    {J : Ideal A}
    (hle : IsLocalRing.maximalIdeal A ≤
      J ⊔ IsLocalRing.maximalIdeal A ^ 2 ⊔ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le.solution
