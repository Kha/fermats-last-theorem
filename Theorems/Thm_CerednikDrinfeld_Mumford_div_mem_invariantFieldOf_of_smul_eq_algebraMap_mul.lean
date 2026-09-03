import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (Γ : Subgroup G) (u : G → K) (x y : FractionRing M)
    (hx : ∀ γ : G, γ ∈ Γ → γ • x = algebraMap K (FractionRing M) (u γ) * x)
    (hy : ∀ γ : G, γ ∈ Γ → γ • y = algebraMap K (FractionRing M) (u γ) * y) :
    x / y ∈ invariantFieldOf K G M Γ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul.solution
