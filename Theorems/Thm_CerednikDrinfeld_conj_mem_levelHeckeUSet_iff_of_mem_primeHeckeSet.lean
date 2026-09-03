import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_conj_mem_levelHeckeUSet_iff_of_mem_primeHeckeSet

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.conj_mem_levelHeckeUSet_iff_of_mem_primeHeckeSet
    {a b : ℚ} {Λ R : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hR : QuaternionAlgebra.IsOrder R) (hRΛ : R ≤ Λ)
    {q ℓ : ℕ} (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    {β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hβ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    n⁻¹ * β * n ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ ↔ β ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_conj_mem_levelHeckeUSet_iff_of_mem_primeHeckeSet.solution
