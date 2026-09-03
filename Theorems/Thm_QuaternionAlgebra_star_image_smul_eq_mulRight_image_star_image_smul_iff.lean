import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff

set_option autoImplicit false
open scoped Quaternion Pointwise

theorem QuaternionAlgebra.star_image_smul_eq_mulRight_image_star_image_smul_iff
    {a b : ℚ} (I J : Submodule ℤ ℍ[ℚ, a, b]) (d d' c : (ℍ[ℚ, a, b])ˣ) :
    star '' ((d' • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
        (· * (c : ℍ[ℚ, a, b])) '' (star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) ↔
      J = (d'⁻¹ * star c * d) • I := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_star_image_smul_eq_mulRight_image_star_image_smul_iff.solution
