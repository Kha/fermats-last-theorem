import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.one_cup_and_cup_one
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) :
    (∀ (b : ℕ) (β : F.cochain 𝒦 b),
        F.cup 𝒦 0 b b (Nat.zero_add b) (fun s => (1 : Γ(V, 𝒦.inter s))) β = β) ∧
      (∀ (a : ℕ) (α : (OModulePresheaf.unit π).cochain 𝒦 a),
        (OModulePresheaf.unit π).cup 𝒦 a 0 a (Nat.add_zero a) α (fun s => (1 : Γ(V, 𝒦.inter s))) = α) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_one_cup_and_cup_one.solution
