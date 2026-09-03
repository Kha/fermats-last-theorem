import Mathlib
import P2M.Util
import P2M.Sol.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton

set_option autoImplicit false

universe u

theorem Module.finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (H : Type u) [AddCommGroup H] [Module S H] [Module k H] [IsScalarTower k S H] [Module.Finite S H]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ 𝔪 : MaximalSpectrum S, 𝔪 ∉ T → Subsingleton (LocalizedModule 𝔪.asIdeal.primeCompl H)) :
    Module.Finite k H ∧ IsFiniteLength S H ∧
      (Module.finrank k H : ℕ∞) =
        ∑ 𝔪 ∈ T, Module.length (Localization.AtPrime 𝔪.asIdeal) (LocalizedModule 𝔪.asIdeal.primeCompl H) := by p2m_exact_reverting @_root_.P2MW.S_Module_finite_and_finrank_eq_sum_length_localizedModule_of_forall_subsingleton.solution
