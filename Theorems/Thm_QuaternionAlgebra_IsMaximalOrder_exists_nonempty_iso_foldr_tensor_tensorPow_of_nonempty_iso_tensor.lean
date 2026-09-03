import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

theorem QuaternionAlgebra.IsMaximalOrder.exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {X : Scheme.{u}} (Φ : ↥Λ → ↥Λ → X.Modules)
    (hΦ_left : ∀ y y' z : ↥Λ, Nonempty (Φ (y + y') z ≅ Φ y z ⊗ Φ y' z))
    (hΦ_right : ∀ y z z' : ↥Λ, Nonempty (Φ y (z + z') ≅ Φ y z ⊗ Φ y z')) :
    ∃ (n : ℕ) (w : Fin n → ↥Λ) (m : Fin n → ℕ),
      0 < n ∧ (∀ i, 0 < m i) ∧ (∀ i, (w i : ℍ[ℚ, a, b]) ≠ 0) ∧
      ∀ x : ↥Λ, Nonempty
        (List.foldr (fun M N => M ⊗ N) (𝟙_ X.Modules)
            (List.ofFn fun i : Fin n =>
              (Φ (w i) ⟨(w i : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 x.2⟩).tensorPow (m i)) ≅
          List.foldr (fun M N => M ⊗ N) (𝟙_ X.Modules)
            (List.ofFn fun i : Fin n =>
              (Φ ⟨(w i : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 (star x).2⟩ (w i)).tensorPow (m i))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor.solution
