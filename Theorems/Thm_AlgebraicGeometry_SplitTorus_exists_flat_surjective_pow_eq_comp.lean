import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp
    {S : Type u} [CommRing S] (t m : ℕ) (hm : 0 < m)
    {U : Scheme.{u}} (hU : U ⟶ Spec (CommRingCat.of S)) (τ : U ⟶ SplitTorus.torusScheme S t)
    (hτ : τ ≫ SplitTorus.torusStr S t = hU) :
    ∃ (U' : Scheme.{u}) (c : U' ⟶ U) (_ : Flat c) (_ : Surjective c) (_ : LocallyOfFinitePresentation c)
      (σ : U' ⟶ SplitTorus.torusScheme S t),
      σ ≫ SplitTorus.torusStr S t = c ≫ hU ∧
      σ ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ)))) = c ≫ τ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp.solution
