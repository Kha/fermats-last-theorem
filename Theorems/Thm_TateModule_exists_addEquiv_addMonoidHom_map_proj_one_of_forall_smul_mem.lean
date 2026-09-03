import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem

set_option autoImplicit false

theorem TateModule.exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (P : Submodule ℤ_[p] ↥(TateModule p M))
    (hsat : ∀ x : ↥(TateModule p M), (p : ℤ_[p]) • x ∈ P → x ∈ P)
    (N : Type*) [AddCommGroup N] (hN : ∀ y : N, p • y = 0) :
    ∃ ρ : (↥P →+ N) ≃+ (↥((P.toAddSubgroup).map (TateModule.proj p M 1)) →+ N),
      (∀ (φ : ↥P →+ N) (x : ↥P) (a : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a : M) = TateModule.proj p M 1 (x : ↥(TateModule p M)) → ρ φ a = φ x) ∧
      (∀ (T : ↥(TateModule p M) →ₗ[ℤ_[p]] ↥(TateModule p M)) (t : M →+ M)
        (hTt : ∀ x : ↥(TateModule p M), TateModule.proj p M 1 (T x) = t (TateModule.proj p M 1 x))
        (hTP : ∀ x ∈ P, T x ∈ P)
        (φ : ↥P →+ N) (a a' : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a' : M) = t (a : M) → ρ (φ.comp (T.restrict hTP).toAddMonoidHom) a = ρ φ a') := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem.solution
