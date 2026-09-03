import Mathlib
import Theorems.Thm_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia
import P2M.Util
import P2M.Sol.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq
    {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P]
    [PerfectField (IsLocalRing.ResidueField ↥(P.comap (FixedPoints.subfield G F).subtype))]
    (n : ℕ) (hn : Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} = n) :
    ∀ (g : G) (Q : ValuationSubring F), Q = g • P →
      ∀ (j : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥Q),
      (∀ r, ((j r : ↥Q) : F) = ((r : ↥(FixedPoints.subfield G F)) : F)) →
      Ideal.map j (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype))
        = IsLocalRing.maximalIdeal ↥Q ^ n := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_pow_of_eq_smul_of_natCard_eq.solution
