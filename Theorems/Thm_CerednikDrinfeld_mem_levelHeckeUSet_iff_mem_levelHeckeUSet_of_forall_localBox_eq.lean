import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq
    {a b : ℚ} {Λ S R : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (hSR : S ≤ R) (hRΛ : R ≤ Λ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → Submodule.localBox S v = Submodule.localBox R v)
    {β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hβ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    β ∈ CerednikDrinfeld.levelHeckeUSet Λ S ℓ ↔ β ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq.solution
