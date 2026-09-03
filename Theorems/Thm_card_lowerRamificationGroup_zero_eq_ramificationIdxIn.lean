import Definitions.Def_DifferentFiltrationFormula
import Mathlib.NumberTheory.RamificationInertia.Galois
import P2M.Util
import P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn

theorem card_lowerRamificationGroup_zero_eq_ramificationIdxIn
    {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [MulSemiringAction G B]
    [IsDedekindDomain A] [Module.Finite A B] [IsGaloisGroup G A B] [Finite G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Nat.card (IsLocalRing.lowerRamificationGroup B G 0)
      = (IsLocalRing.maximalIdeal A).ramificationIdxIn B := by p2m_exact_reverting @_root_.P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution
