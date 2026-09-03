import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (C : Fin k → Type) [∀ i, CommRing (C i)] [∀ i, Algebra 𝒪 (C i)] [∀ i, Algebra B (C i)]
    [∀ i, IsScalarTower 𝒪 B (C i)] [∀ i, IsLocalization.Away (f i) (C i)]
    (C₂ : Fin k → Fin k → Type) [∀ i j, CommRing (C₂ i j)] [∀ i j, Algebra 𝒪 (C₂ i j)] [∀ i j, Algebra B (C₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (C₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (C₂ i j)]
    (ρ₁ : ∀ i j, C i →ₐ[B] C₂ i j) (ρ₂ : ∀ i j, C j →ₐ[B] C₂ i j)
    (d : ∀ i, (Omega K π).obj (C i))
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j)) :
    ∃! d₀ : (Omega K π).obj B, ∀ i, (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) d₀ = d i := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top.solution
