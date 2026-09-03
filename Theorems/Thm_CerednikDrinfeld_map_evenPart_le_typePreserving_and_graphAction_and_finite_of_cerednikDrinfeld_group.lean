import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
attribute [-simp] CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld
theorem CerednikDrinfeld.map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)
    :
    Γ'.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) ∧
    Mumford.GraphAction ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀) ∧
    (∀ d : (BruhatTits.tree 𝒪 K₀).Dart, Finite (MulAction.stabilizer (↥(Γ'.map ρ)) d)) ∧
    Finite (Mumford.QuotVert ↥(Γ'.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
    Finite (Mumford.QuotEdge ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀)) ∧
    (∃ γ : G, γ ∈ Γ ∧ ρ γ ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀)) ∧
    (∀ x : G, x ∈ Γ → (x ∈ Γ' ↔ ρ x ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))) ∧

    Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree 𝒪 K₀) ∧
    (∀ d : (BruhatTits.tree 𝒪 K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d)) ∧
    Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
    Finite (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree 𝒪 K₀)) ∧
    Γ'.relIndex Γ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group.solution
