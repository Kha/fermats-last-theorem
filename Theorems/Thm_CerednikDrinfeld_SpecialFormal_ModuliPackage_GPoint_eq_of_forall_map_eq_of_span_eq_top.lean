import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_eq_of_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.eq_of_forall_map_eq_of_span_eq_top
    {p : ℕ} [Fact p.Prime] {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]
    {M : ModuliPackage.{0, 0} p O} (hM : M.IsZariskiSheaf)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra 𝒪 (L i)] [∀ i, Algebra B (L i)] [∀ i, IsScalarTower 𝒪 B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (x y : ModuliPackage.GPoint 𝒪 M B)
    (h : ∀ i, x.map (IsScalarTower.toAlgHom 𝒪 B (L i)) = y.map (IsScalarTower.toAlgHom 𝒪 B (L i))) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_eq_of_forall_map_eq_of_span_eq_top.solution
