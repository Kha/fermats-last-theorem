import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_isCompact_forall_exists_fuchsianGroup_smul_mem {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧
      ∀ τ : UpperHalfPlane, ∃ γ ∈ fuchsianGroup R ι, γ • τ ∈ K := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_isCompact_forall_exists_fuchsianGroup_smul_mem.solution
