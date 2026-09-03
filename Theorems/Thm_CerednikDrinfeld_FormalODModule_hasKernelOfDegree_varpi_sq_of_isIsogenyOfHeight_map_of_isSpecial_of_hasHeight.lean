import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] (j₀ : Zp2 p →+* k)
    (Φ : FormalODModule p k) (hΦs : Φ.IsSpecial j₀) (hΦ4 : Φ.HasHeight 4)
    {L : Type} [CommRing L] [IsNoetherianRing L] (hLp : IsNilpotent ((p : ℕ) : L))
    (f : k →+* L ⧸ pIdeal p L) (X : FormalODModule p L) (ρ : Series (L ⧸ pIdeal p L)) (h : ℕ)
    (hρ : FormalODModule.IsIsogenyOfHeight (Φ.map f) (X.map (Ideal.Quotient.mk (pIdeal p L))) ρ h) :
    FormalODModule.HasKernelOfDegree X.varpi (p ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight.solution
