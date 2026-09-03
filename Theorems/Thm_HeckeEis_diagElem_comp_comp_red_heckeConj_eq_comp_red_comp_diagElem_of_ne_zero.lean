import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero

set_option autoImplicit false

theorem HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
    (N q : ℕ) [Fact q.Prime] (K : Type) [CommRing K]
    {Wc : Type} [AddCommGroup Wc] [Module K Wc] (W : Representation K (CuspidalType.GL2 q) Wc)
    (red : CongruenceSubgroup.Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (CongruenceSubgroup.Gamma0 N).subtype)
    (ℓ : ℕ) [NeZero ℓ] (h : (ℓ : ZMod q) ≠ 0) (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) ∘ₗ (W.comp red) (HeckeEis.heckeConj N ℓ u) =
      (W.comp red) (u : CongruenceSubgroup.Gamma0 N) ∘ₗ W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero.solution
