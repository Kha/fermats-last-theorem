import Mathlib
import Definitions.Def_Deformations_LocalSplitting
import P2M.Util
import P2M.Sol.S_TaylorWiles_isEigenIdempotent_smul_sub

set_option autoImplicit false

universe u v

open Matrix
theorem TaylorWiles.isEigenIdempotent_smul_sub {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b v : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hv : v * (a - b) = 1) :
    TaylorWiles.IsEigenIdempotent M a b (v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A))) := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_isEigenIdempotent_smul_sub.solution
