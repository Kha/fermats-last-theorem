import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion
attribute [-simp] Submodule.finiteAdeleEvalAt_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer Λ))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer Λ))]
    (ℓ ℓ' : ℕ) (hℓ : ℓ.Coprime ℓ')
    (T T' : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hT : T ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ) (hT' : T' ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ')
    (hTl : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, u * s ∈ T)
    (hTr : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, s * u ∈ T)
    (hT'l : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T', u * s ∈ T')
    (hT'r : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T', s * u ∈ T')

    (hTfin : {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ | ∃ h ∈ T,
      (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c}.Finite)
    (hT'fin : {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ | ∃ h ∈ T',
      (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c}.Finite) :
    Commute (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer Λ) T)
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer Λ) T') := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime.solution
