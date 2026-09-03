import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit
    (a b : ℚ) (p : ℕ) (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∉ v.asIdeal →
      ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit.solution
