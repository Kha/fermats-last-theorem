import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (X Y : Subgroup G) (hX : X ≤ typePreserving G 𝒯 w₀) (hY : Y ≤ typePreserving G 𝒯 w₀)
    (g : G) (hg : g ∈ typePreserving G 𝒯 w₀)
    (hXY : ∀ x ∈ X, g⁻¹ * x * g ∈ Y)
    (hidx : (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y ≠ 0)
    (hfinV : ∀ v : W, Finite (stabilizer (↥Y) v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer (↥Y) d))

    {E V E' V' : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    [Fintype E'] [DecidableEq E'] [Fintype V'] [DecidableEq V']
    (D : DegeneracyData E V) (eV : QuotVert (↥X) W ≃ V) (eE : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.fst))
    (hDb : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.snd))
    (hDw : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (stabilizer (↥X) e.1.out))
    (D' : DegeneracyData E' V') (eV' : QuotVert (↥Y) W ≃ V') (eE' : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E')
    (hDa' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.a (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.fst))
    (hDb' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.b (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.snd))
    (hDw' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D'.w (eE' e) : ℕ) = Nat.card (stabilizer (↥Y) e.1.out)) :
    ∃ μ : D.FiniteHom D',
      (∀ v : W, μ.mapV (eV (Quotient.mk (orbitRel (↥X) W) v)) = eV' (Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • v))) ∧
      (∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
        ((eE'.symm (μ.mapE (eE e))) : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}).1 = Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • e.1.out)) ∧
      (μ.degTotal : ℕ) = (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le.solution
