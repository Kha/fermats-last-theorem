import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cup_cup

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cup_cup
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) (a b c nab n : ℕ) (hab : a + b = nab) (hn : nab + c = n)
    (α : (OModulePresheaf.unit π).cochain 𝒦 a) (β : (OModulePresheaf.unit π).cochain 𝒦 b) (γ : F.cochain 𝒦 c) :
    F.cup 𝒦 nab c n hn ((OModulePresheaf.unit π).cup 𝒦 a b nab hab α β) γ =
      F.cup 𝒦 a (b + c) n (by omega) α (F.cup 𝒦 b c (b + c) rfl β γ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cup_cup.solution
