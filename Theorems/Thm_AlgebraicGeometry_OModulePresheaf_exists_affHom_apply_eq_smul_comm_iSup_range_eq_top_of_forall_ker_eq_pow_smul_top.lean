import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A) {s : ℕ} (g : Fin s → A) (hg : Ideal.span (Set.range g) = I)
    {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf π) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : V.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : V.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf π) (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : V.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : V.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (K k) (K (k + 1)),
      (∀ (m : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1) (y : (F (k + 1 + 1)).obj U.1),
          (φ (k + 1)).app U y = (j k).app U x → (j (k + 1)).app U ((θ m k).app U x) = g m • y) ∧
      (∀ (m m' : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1),
          (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x)) ∧
      (∀ (k : ℕ) (U : V.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.solution
