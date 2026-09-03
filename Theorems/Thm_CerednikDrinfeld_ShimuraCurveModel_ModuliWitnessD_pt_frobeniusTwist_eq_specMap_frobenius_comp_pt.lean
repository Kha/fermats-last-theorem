import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_CerednikDrinfeld_QMModuliWitnessD
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM IsDedekindDomain
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D)
    (k : Type) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Ā Āℓ : FakeEllipticCurve Λ N k) (hFV : FakeEllipticCurve.HasFrobeniusVerschiebung ℓ Ā Āℓ) :
    (w.pt k sk Āℓ).1 = Spec.map (CommRingCat.ofHom (frobenius k ℓ)) ≫ (w.pt k sk Ā).1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt.solution
