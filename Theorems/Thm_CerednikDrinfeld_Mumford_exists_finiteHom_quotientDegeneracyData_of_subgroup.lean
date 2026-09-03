import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_finiteHom_quotientDegeneracyData_of_subgroup
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (Γ' : Subgroup G) [GraphAction (↥Γ') 𝒯] [Γ'.FiniteIndex]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)]
    [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotVert (↥Γ') W)] [DecidableEq (QuotVert (↥Γ') W)] :
    ∃ μ : (quotientDegeneracyData (↥Γ') 𝒯).FiniteHom (quotientDegeneracyData G 𝒯),
      (∀ e' : QuotEdge (↥Γ') 𝒯, μ.mapE e' = Quotient.mk (orbitRel G 𝒯.Dart) e'.out) ∧
      (∀ v' : QuotVert (↥Γ') W, μ.mapV v' = Quotient.mk (orbitRel G W) v'.out) ∧
      (∀ e' : QuotEdge (↥Γ') 𝒯,
        (μ.deg e' : ℕ) * Nat.card (stabilizer (↥Γ') e'.out) = Nat.card (stabilizer G e'.out)) ∧
      (∀ v' : QuotVert (↥Γ') W,
        (μ.degV v' : ℕ) * Nat.card (stabilizer (↥Γ') v'.out) = Nat.card (stabilizer G v'.out)) ∧
      (μ.degTotal : ℕ) = Γ'.index := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.solution
