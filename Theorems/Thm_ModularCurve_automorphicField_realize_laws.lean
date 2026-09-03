import Definitions.Def_ModularCurve_AutomorphicField
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_automorphicField_realize_laws

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.automorphicField_realize_laws
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] :

    (∀ (a s : ↥ModularCurve.holRing), s ≠ 0 → ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.merRealize
          (algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) a /
            algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) s) z =
        (a : ℍ → ℂ) z / (s : ℍ → ℂ) z) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ),
      MeromorphicAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ)) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x + y) z =
        ModularCurve.automorphicField.realize x z + ModularCurve.automorphicField.realize y z) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x * y) z =
        ModularCurve.automorphicField.realize x z * ModularCurve.automorphicField.realize y z) ∧
    (∀ (c : ℂ) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (algebraMap ℂ ↥(ModularCurve.automorphicField Γ) c) z = c) ∧
    (∀ x y : ↥(ModularCurve.automorphicField Γ),
      (∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
        ModularCurve.automorphicField.realize x z = ModularCurve.automorphicField.realize y z) → x = y) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)), ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize x (γ • z) = ModularCurve.automorphicField.realize x z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_automorphicField_realize_laws.solution
