import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq

universe u

theorem IsLocalRing.exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀)
      (_ : IsLocalHom (algebraMap R R₀)) (x : Fin (n + 1) → R₀),
      ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal R₀ → i = j := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq.solution
