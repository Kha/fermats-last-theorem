import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_map_iso

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.map_iso
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F G : FormalGroup T) (φ : FormalGroup.LawIso F G)
    (q : ℕ) (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (h : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    G.IsDrinfeldBasisAdic I q (φ.toLawHom.appAdic I x₀) (φ.toLawHom.appAdic I x₁) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_map_iso.solution
