import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_cup

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.d_cup
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π)
    (𝒦 : V.OrderedAffineCover) (a b n : ℕ) (h : a + b = n)
    (α : (OModulePresheaf.unit π).cochain 𝒦 a) (β : F.cochain 𝒦 b) :
    F.d 𝒦 n (F.cup 𝒦 a b n h α β) =
      F.cup 𝒦 (a + 1) b (n + 1) (by omega) ((OModulePresheaf.unit π).d 𝒦 a α) β +
        ((-1 : ℤ) ^ a) • F.cup 𝒦 a (b + 1) (n + 1) (by omega) α (F.d 𝒦 b β) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_cup.solution
