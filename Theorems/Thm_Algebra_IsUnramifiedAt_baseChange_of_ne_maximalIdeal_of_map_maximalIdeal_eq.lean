import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq

set_option autoImplicit false

open TensorProduct

theorem Algebra.IsUnramifiedAt.baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [IsLocalRing R] [IsLocalRing R']
    [Algebra R R'] (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Algebra R S] [Module.Finite R S]
    (hS : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt R 𝔮) :
    ∀ (𝔔 : Ideal (R' ⊗[R] S)) [𝔔.IsPrime], ¬ 𝔔.IsMaximal → Algebra.IsUnramifiedAt R' 𝔔 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq.solution
