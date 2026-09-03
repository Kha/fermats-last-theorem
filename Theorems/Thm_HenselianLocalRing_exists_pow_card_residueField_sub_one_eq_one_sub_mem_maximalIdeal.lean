import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal

theorem HenselianLocalRing.exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Finite (IsLocalRing.ResidueField A)] {u : A} (hu : IsUnit u) :
    ∃ ω : A, ω ^ (Nat.card (IsLocalRing.ResidueField A) - 1) = 1 ∧
      ω - u ∈ IsLocalRing.maximalIdeal A := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal.solution
