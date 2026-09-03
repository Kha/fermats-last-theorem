import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (w : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hpw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal)
    (φw : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hφw : ∀ c : w.adicCompletion ℚ,
      φw ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)))
    (h : GL (Fin 2) (w.adicCompletion ℚ))
    (hRw : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      x ∈ Submodule.localBox R w ↔
        ∀ i j, (((h⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
          φw x * (h : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ)
    {N : ℕ} [NeZero N] (hpN : p ∣ N) (hppN : ¬ p ^ 2 ∣ N)
    (φ : ↥R →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ R, φ ⟨1, h1⟩ = 1)
    (hφmul : ∀ (x y : ↥R) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ R),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥R, φ x = 0 ↔ ∃ y : ↥R, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (R₀ : Submodule ℤ ℍ[ℚ, a, b]) (hR₀ : ∀ x : ↥R, (x : ℍ[ℚ, a, b]) ∈ R₀ ↔ φ x 1 0 = 0) (hR₀R : R₀ ≤ R) :
    ∃ g : GL (Fin 2) (w.adicCompletion ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔
          ∀ i j, (((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R₀ w ↔
          (∀ i j, (((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ) ∧
          (∀ i j, (Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ))⁻¹] *
            ((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ)]) i j
              ∈ w.adicCompletionIntegers ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.solution
