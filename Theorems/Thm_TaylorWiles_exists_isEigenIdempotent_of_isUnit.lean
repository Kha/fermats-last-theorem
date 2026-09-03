import Mathlib
import Definitions.Def_Deformations_LocalSplitting
import P2M.Util
import P2M.Sol.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit

set_option autoImplicit false

universe u v

open Matrix
theorem TaylorWiles.exists_isEigenIdempotent_of_isUnit {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit.solution
