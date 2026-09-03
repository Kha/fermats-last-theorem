import Mathlib
import Definitions.Def_SemilocalAdicCompletion
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints

set_option autoImplicit false

open scoped Pointwise
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints
    {O : Type*} [CommRing O] {S : Type*} [CommRing S] [IsNoetherianRing S] [Algebra O S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G O S]
    (J : Ideal O) [IsArtinianRing (S ⧸ J.map (algebraMap O S))]
    (P : Ideal S) [P.IsMaximal] (hJP : J.map (algebraMap O S) ≤ P)
    (htrans : ∀ Q : Ideal S, Q.IsMaximal → J.map (algebraMap O S) ≤ Q → ∃ g : G, Q = g • P) :
    (∀ x : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) →
      ∀ d : MulAction.stabilizer G P,
        d • AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x =
          AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x) ∧
    (∀ x y : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) → (∀ g : G, g • y = y) →
      AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x =
        AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP y → x = y) ∧
    (∀ z : AdicCompletion P S, (∀ d : MulAction.stabilizer G P, d • z = z) →
      ∃ x : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) ∧
        AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x = z) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints.solution
