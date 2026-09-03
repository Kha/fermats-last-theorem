import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_inf_cocycle_of_face_cocycle
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (u u' : ∀ s : 𝒱.Idx 1, Γ(Y, 𝒱.inter s)) (huu' : ∀ s : 𝒱.Idx 1, u s * u' s = 1)
    (hcoc : ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (u (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (u (𝒱.face r 0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (u (𝒱.face r 1))) :
    ∃ W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b),
      (∀ a : 𝒱.ι, W a a = 1) ∧ (∀ a b : 𝒱.ι, IsUnit (W a b)) ∧
      (∀ a b c : 𝒱.ι,
        (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
            (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
          (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c)) ∧
      (∀ s : 𝒱.Idx 1,
        (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
          𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) = u s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.solution
