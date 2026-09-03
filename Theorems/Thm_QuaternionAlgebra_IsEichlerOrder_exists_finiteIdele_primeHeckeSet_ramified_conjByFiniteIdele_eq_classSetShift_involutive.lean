import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∃ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))) * u ∧
        ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
          u ∈ Submodule.finiteIdeleStabilizer X) ∧
      ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
        ϖ ∈ primeHeckeSet X p ∧
        Submodule.conjByFiniteIdele X ϖ = X ∧
        (∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
          classSetShift _ ϖ (classSetShift _ ϖ x) = x) ∧
        ∀ m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits R v →
          (∃ c ∈ Submodule.finiteIdeleStabilizer X, m * ϖ = ϖ * m * c) ∧
          (Submodule.conjByFiniteIdele X m = X →
            ∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
              classSetShift _ ϖ (classSetShift _ m x) = classSetShift _ m (classSetShift _ ϖ x)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.solution
