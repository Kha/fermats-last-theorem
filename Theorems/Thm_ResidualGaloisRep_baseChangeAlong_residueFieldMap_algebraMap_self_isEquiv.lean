import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv

theorem ResidualGaloisRep.baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv {𝒪 : Type}
    [CommRing 𝒪] [IsLocalRing 𝒪] (ρ : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)) :
    (ρ.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))).IsEquiv ρ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv.solution
