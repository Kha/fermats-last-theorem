import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W) :
    (∀ x y : W, 𝒯.Adj x y → vertexType 𝒯 w₀ y = vertexType 𝒯 w₀ x + 1) ∧
    (∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w) ∧
    (∃ ε : G →* Multiplicative (ZMod 2),
      (∀ g : G, Multiplicative.toAdd (ε g) = vertexType 𝒯 w₀ (g • w₀)) ∧ ε.ker = typePreserving G 𝒯 w₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter.solution
