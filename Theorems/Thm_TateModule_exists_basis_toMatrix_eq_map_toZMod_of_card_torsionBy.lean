import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_basis_toMatrix_eq_map_toZMod_of_card_torsionBy

set_option autoImplicit false

theorem TateModule.exists_basis_toMatrix_eq_map_toZMod_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ_[ℓ] (TateModule ℓ M))
    (hcard : Nat.card (Submodule.torsionBy ℤ M (ℓ : ℤ)) = ℓ ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    (ι : V →+ M) (hι : Function.Injective ι) (hιr : ∀ m : M, m ∈ ι.range ↔ (ℓ : ℤ) • m = 0) :
    ∃ c : Module.Basis (Fin r) (ZMod ℓ) V, (∀ i, ι (c i) = TateModule.proj ℓ M 1 (b i)) ∧
      ∀ (α : M →+ M) (T : V →ₗ[ZMod ℓ] V), (∀ v, ι (T v) = α (ι v)) →
        LinearMap.toMatrix c c T =
          (LinearMap.toMatrix b b
            (TateModule.rep ℓ M (Module.End ℤ M) α.toIntLinearMap)).map PadicInt.toZMod := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_basis_toMatrix_eq_map_toZMod_of_card_torsionBy.solution
