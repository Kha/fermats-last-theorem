import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents

set_option autoImplicit false

universe u v

theorem Bialgebra.existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type v} [CommRing H] [Bialgebra R H]
    {ι : Type} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e) :
    ∃! i : ι, Coalgebra.counit (R := R) (e i) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents.solution
