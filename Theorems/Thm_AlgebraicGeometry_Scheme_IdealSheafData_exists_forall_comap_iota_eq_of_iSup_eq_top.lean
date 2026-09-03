import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
    {Y : Scheme.{u}} {ι : Type u} (𝒰 : ι → Y.Opens) (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (I : ∀ j, (𝒰 j : Scheme.{u}).IdealSheafData)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) :
    ∃ I₀ : Y.IdealSheafData, ∀ j, I₀.comap (𝒰 j).ι = I j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.solution
