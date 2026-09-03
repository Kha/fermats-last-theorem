import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X Y : FormalODModule p B) (ρ : Series B) (h : ℕ)
    (hρ : FormalODModule.IsIsogenyOfHeight X Y ρ h) (hX : X.HasHeight 4) :
    Y.HasHeight 4 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight.solution
