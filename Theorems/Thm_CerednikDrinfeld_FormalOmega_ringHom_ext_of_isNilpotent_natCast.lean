import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast

set_option autoImplicit false

theorem CerednikDrinfeld.FormalOmega.ringHom_ext_of_isNilpotent_natCast
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (C : Type) [CommRing C] (hC : IsNilpotent ((r : ℕ) : C)) (f g : 𝒪 →+* C) : f = g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast.solution
