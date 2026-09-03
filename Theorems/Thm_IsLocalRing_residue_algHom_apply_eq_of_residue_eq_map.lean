import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Algebra.Hom
import P2M.Util
import P2M.Sol.S_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map

set_option autoImplicit false

theorem IsLocalRing.residue_algHom_apply_eq_of_residue_eq_map
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
    (πT : L →ₐ[𝒪] 𝒪) (z : L) (x : IsLocalRing.ResidueField 𝒪)
    (hz : IsLocalRing.residue L z = IsLocalRing.ResidueField.map (algebraMap 𝒪 L) x) :
    IsLocalRing.residue 𝒪 (πT z) = x := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map.solution
