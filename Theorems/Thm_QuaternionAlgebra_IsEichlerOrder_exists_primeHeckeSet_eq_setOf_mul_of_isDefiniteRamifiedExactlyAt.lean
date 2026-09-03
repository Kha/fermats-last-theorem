import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {S : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hS : IsEichlerOrder S N)
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer S))] :
    ∃ π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      π ∈ primeHeckeSet S q' ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        u ∈ Submodule.finiteIdeleStabilizer S ↔ π * u * π⁻¹ ∈ Submodule.finiteIdeleStabilizer S) ∧
      (∃ u ∈ Submodule.finiteIdeleStabilizer S,
        π * π = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr hq'.ne_zero))) * u) ∧
      primeHeckeSet S q' = {h | ∃ u ∈ Submodule.finiteIdeleStabilizer S, h = π * u} ∧
      classSetHeckeMatrix (Submodule.finiteIdeleStabilizer S) (primeHeckeSet S q') =
        Matrix.of (fun i j : ClassSet (Submodule.finiteIdeleStabilizer S) =>
          if classSetShift (Submodule.finiteIdeleStabilizer S) π j = i then (1 : ℤ) else 0) ∧
      (∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele S π ↔
        h ∈ S ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.solution
