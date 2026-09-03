import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P]
    [PerfectField (IsLocalRing.ResidueField ↥(P.comap (FixedPoints.subfield G F).subtype))] :
    Ideal.map (show ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥P from
        { toFun := fun r => ⟨(FixedPoints.subfield G F).subtype r, r.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun a b => Subtype.ext (map_add _ _ _) })
        (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype)) =
      IsLocalRing.maximalIdeal ↥P ^
        Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_map_maximalIdeal_comap_fixedPoints_eq_maximalIdeal_pow_card_inertia.solution
