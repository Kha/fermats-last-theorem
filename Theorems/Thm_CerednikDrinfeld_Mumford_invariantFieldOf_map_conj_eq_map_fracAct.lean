import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.invariantFieldOf_map_conj_eq_map_fracAct
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M] (g : G) (Γ : Subgroup G) :
    invariantFieldOf K G M (Γ.map (MulAut.conj g).toMonoidHom) =
      (invariantFieldOf K G M Γ).map (fracAct G M g).toRingHom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct.solution
