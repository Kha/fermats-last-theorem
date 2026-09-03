import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_isCompact_finset_forall_sl

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_isCompact_finset_forall_sl {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (C : Set (Matrix (Fin 2) (Fin 2) ℝ)) (S : Finset ℚ), IsCompact C ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ r ∈ R, r ≠ 0 ∧ nrd r ∈ S ∧
        ι r * (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ C := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_isCompact_finset_forall_sl.solution
