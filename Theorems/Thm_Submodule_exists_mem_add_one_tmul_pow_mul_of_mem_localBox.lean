import Mathlib
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_mem_add_one_tmul_pow_mul_of_mem_localBox
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) (k : ℕ)
    {Y : D ⊗[ℚ] v.adicCompletion ℚ} (hY : Y ∈ Submodule.localBox Λ v) :
    ∃ z ∈ Λ, ∃ E ∈ Submodule.localBox Λ v,
      Y = z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) + ((1 : D) ⊗ₜ[ℚ] ((p : v.adicCompletion ℚ) ^ k)) * E := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox.solution
