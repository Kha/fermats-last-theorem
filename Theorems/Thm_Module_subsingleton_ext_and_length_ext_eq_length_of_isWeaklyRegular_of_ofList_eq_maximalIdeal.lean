import Mathlib
import P2M.Util
import P2M.Sol.S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal

set_option autoImplicit false

universe u

open CategoryTheory

theorem Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htors : ∃ k : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ k, ∀ z : N, a • z = 0) :
    (∀ i : ℕ, i ≠ rs.length → Subsingleton (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) i)) ∧
      Module.length R (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) rs.length) = Module.length R N := by p2m_exact_reverting @_root_.P2MW.S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal.solution
