import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_primeHeckeSet_eq_and_heckeKernel_eq_of_ramified
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.primeHeckeSet_eq_and_heckeKernel_eq_of_ramified
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {X : Submodule ℤ ℍ[ℚ, a, b]} {M : ℕ} (hX : IsEichlerOrder X M)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hϖ : ϖ ∈ primeHeckeSet X p) :
    primeHeckeSet X p =
      {h | ∃ u ∈ Submodule.finiteIdeleStabilizer X, h = ϖ * u} ∧
    (∀ x y : ClassSet (Submodule.finiteIdeleStabilizer X),
      (classSetShift _ ϖ x = y → heckeKernel (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p) x y = 1) ∧
      (classSetShift _ ϖ x ≠ y → heckeKernel (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p) x y = 0)) ∧
    ∀ [Fintype (ClassSet (Submodule.finiteIdeleStabilizer X))] (f : ClassSet (Submodule.finiteIdeleStabilizer X) → ℤ),
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p)).mulVec f =
        f ∘ classSetShift _ ϖ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_primeHeckeSet_eq_and_heckeKernel_eq_of_ramified.solution
