import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [Mumford.GraphAction G 𝒯]
    (hconn : 𝒯.Connected) (hbip : 𝒯.Colorable 2) (w₀ : W) :
    (∃ φ : G →* Multiplicative (ZMod 2), φ.ker = Mumford.typePreserving G 𝒯 w₀) ∧
      (Mumford.typePreserving G 𝒯 w₀).index ∣ 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two.solution
