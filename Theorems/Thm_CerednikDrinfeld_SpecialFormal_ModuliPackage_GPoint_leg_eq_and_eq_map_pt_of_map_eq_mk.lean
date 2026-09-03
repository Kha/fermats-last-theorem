import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_leg_eq_and_eq_map_pt_of_map_eq_mk

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.leg_eq_and_eq_map_pt_of_map_eq_mk
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)} {M : ModuliPackage.{0, 0} r Onr}
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    {B L : Type} [CommRing B] [Algebra 𝒪 B] [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    (x : ModuliPackage.GPoint 𝒪 M B) (χ : Onr →ₐ[𝒪] L) (hL : IsNilpotent (r : L)) (t : Rigidified r Φ L)
    (h : x.map φ = ⟨χ, hL, η L (χ : Onr →+* L) hL t⟩) :
    χ = φ.comp x.ψ ∧
      η L ((φ : B →+* L).comp (x.ψ : Onr →+* B)) hL t =
        M.map (ψ' := (φ : B →+* L).comp (x.ψ : Onr →+* B)) x.nilp hL (φ : B →+* L) rfl x.pt := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_leg_eq_and_eq_map_pt_of_map_eq_mk.solution
