import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓq' : ℓ ≠ q')
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hg : g ∈ QuaternionAlgebra.primeHeckeSet R ℓ) :
    QuaternionAlgebra.primeHeckeSet R ℓ =
      DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer R) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer.solution
