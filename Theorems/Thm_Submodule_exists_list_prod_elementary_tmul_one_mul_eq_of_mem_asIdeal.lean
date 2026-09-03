import Mathlib
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_list_prod_elementary_tmul_one_mul_eq_of_mem_asIdeal

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_list_prod_elementary_tmul_one_mul_eq_of_mem_asIdeal
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hone : (1 : D) ∈ Λ) (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (l : List (Bool × (D ⊗[ℚ] v.adicCompletion ℚ))) :
    ∃ l' : List (Bool × D),
      (∀ e ∈ l', ∃ n : ℕ, ((p ^ n : ℕ) : ℤ) • e.2 ∈ Λ) ∧
      ∃ X Y : Matrix (Fin 2) (Fin 2) (D ⊗[ℚ] v.adicCompletion ℚ),
        (∀ i j, X i j ∈ Submodule.localBox Λ v) ∧ (∀ i j, Y i j ∈ Submodule.localBox Λ v) ∧
        X * Y = 1 ∧ Y * X = 1 ∧
        (l.map fun e => if e.1 then !![1, e.2; 0, 1] else !![1, 0; e.2, 1]).prod =
          ((l'.map fun e => (e.1, e.2 ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))).map
              fun e => if e.1 then !![1, e.2; 0, 1] else !![1, 0; e.2, 1]).prod * X := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_list_prod_elementary_tmul_one_mul_eq_of_mem_asIdeal.solution
