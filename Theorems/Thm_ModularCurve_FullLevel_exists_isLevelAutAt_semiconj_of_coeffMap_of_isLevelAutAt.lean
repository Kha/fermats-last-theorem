import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.FullLevel~exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot CongruenceSubgroup"
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (m : ℕ) [NeZero m] (hqm : q ∣ m) (hmM : Nat.Coprime m M')
    (ξ : L) (hξ : IsPrimitiveRoot ξ m)
    (K : IntermediateField L (LaurentSeries L))
    (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (g : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K g →
        ∃ (γ' : SL(2, ℤ)) (g' : ↥K ≃ₐ[L] ↥K),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          (∀ x : ↥K, τ (g' x) = g (τ x)) ∧
          ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ' K g' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt.solution
