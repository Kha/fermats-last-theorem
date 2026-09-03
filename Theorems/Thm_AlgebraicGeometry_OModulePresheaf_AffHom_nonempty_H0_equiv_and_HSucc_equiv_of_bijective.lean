import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective.solution
