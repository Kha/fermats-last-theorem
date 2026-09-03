import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.QM.forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)

    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
    (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
    (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R) (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
        (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) l)) =
          (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) l))) ∧

    (∀ β : (Fin 2 → Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → Fin 2 → ZMod N),
        (∀ (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
            β (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) = (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((β w) l))) →
        ∃ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), ∀ w : Fin 2 → Fin 2 → ZMod N, β w = (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l))) ∧

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R),
        (∀ w : Fin 2 → Fin 2 → ZMod N, (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) = 0) ↔
          ∃ y ∈ R, x = (N : ℚ) • y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.solution
