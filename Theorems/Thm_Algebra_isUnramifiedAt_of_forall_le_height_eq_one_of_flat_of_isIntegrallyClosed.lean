import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed

set_option autoImplicit false

universe u

theorem Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed
    (O : Type u) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
    (F : Type u) [Field F] [Algebra C F] [IsFractionRing C F] [Algebra K F] [Algebra O F]
    [IsScalarTower O K F] [IsScalarTower O C F] [Algebra.IsSeparable K F]
    (P : Ideal C) [P.IsPrime]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Q ≤ P → Q.height = 1 → Algebra.IsUnramifiedAt O Q) :
    Algebra.IsUnramifiedAt O P := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed.solution
