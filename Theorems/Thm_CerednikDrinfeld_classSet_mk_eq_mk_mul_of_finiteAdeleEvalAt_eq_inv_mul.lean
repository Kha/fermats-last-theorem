import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul
    {a b : ℚ} (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (q : ℕ) [Fact q.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsf : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (hsfv : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hy : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hyv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) y =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) (x * sf) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul.solution
