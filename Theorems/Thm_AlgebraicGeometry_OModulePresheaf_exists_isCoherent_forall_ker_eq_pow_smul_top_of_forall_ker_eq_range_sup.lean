import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
    {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {H G : OModulePresheaf q} (hHq : H.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (h : OModulePresheaf.AffHom H G)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
    (hψs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U))
    (hψk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1)))
    (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G')
      (ψ' : ∀ k, OModulePresheaf.AffHom G' (F k)),
      G'.IsCoherent ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U ∘ₗ ρ.app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ' k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ' k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ' (k + 1)).app U = (ψ' k).app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution
