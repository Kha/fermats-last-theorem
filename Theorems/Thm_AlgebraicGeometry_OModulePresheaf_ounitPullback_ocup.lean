import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_ounitPullback_ocup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.ounitPullback_ocup
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit πY).ocochain 𝒦 a) (β : (OModulePresheaf.unit πY).ocochain 𝒦 b) :
    OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).ocup 𝒦 a b n hn α β) =
      (OModulePresheaf.unit πX).ocup 𝒲 a b n hn
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α)
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_ounitPullback_ocup.solution
