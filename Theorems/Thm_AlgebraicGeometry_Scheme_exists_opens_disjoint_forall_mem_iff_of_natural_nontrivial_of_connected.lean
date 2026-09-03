import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
    {C : Type} [CommRing C] [IsNoetherianRing C] (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]
    (L : Type) [Fintype L] [DecidableEq L]
    (lab : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
      (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → (Scheme.nilpPoints fX).obj S → L)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Nontrivial S']
      (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)) (hS' : (∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1))
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      lab S' hS' ((Scheme.nilpPoints fX).map g x) = lab S hS x) :
    ∃ U : L → X.Opens,
      (∀ l l' : L, l ≠ l' → Disjoint (U l) (U l')) ∧ (⨆ l, U l) = ⊤ ∧
      ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1))
        (x : (Scheme.nilpPoints fX).obj S) (l : L),
        lab S hS x = l ↔ ∀ p : ↥(Spec (CommRingCat.of S)), x.1.base p ∈ U l := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected.solution
