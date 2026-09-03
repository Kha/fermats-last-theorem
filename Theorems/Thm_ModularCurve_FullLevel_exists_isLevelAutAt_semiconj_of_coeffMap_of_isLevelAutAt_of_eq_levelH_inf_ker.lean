import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker

set_option autoImplicit false

open ModularCurve open ModularCurve.FullLevel hiding exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (g : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K g →
        ∃ (γ' : SL(2, ℤ)) (g' : ↥K ≃ₐ[L] ↥K),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          (∀ x : ↥K, τ (g' x) = g (τ x)) ∧
          ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ' K g' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker.solution
