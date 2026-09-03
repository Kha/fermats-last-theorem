import Mathlib
import P2M.Util
import P2M.Sol.S_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin

set_option autoImplicit false

theorem Module.length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (P : Submodule R M) (e : Fin 2 → M) (he : ∀ r, e r ∈ P)
    (heb : ∀ m ∈ P, ∃! w : Fin 2 → R, m = ∑ r, w r • e r)
    (A : Matrix (Fin 2) (Fin 2) R) :
    Module.length R (↥P ⧸ Submodule.comap P.subtype
        (Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r))) =
      Module.length R ((Fin 2 → R) ⧸ LinearMap.range (Matrix.mulVecLin A)) := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin.solution
