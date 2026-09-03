import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliPropsD
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsDedekindDomain CerednikDrinfeld

theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField
    {a b : ℚ} {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ} {D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D)
    (O : Type) [CommRing O] (j : Localization.Away ((D : ℕ) : ℤ) →+* O)
    (i : O →+* AlgebraicClosure ℚ)
    (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (hs : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j) = s)
    [AlgebraicGeometry.IsIntegral ↑w.X] [AlgebraicGeometry.IsIntegral ↑(pullback w.πX s)]

    (eFbar : M.Fbar ≃+* ↥((pullback w.πX s).functionField))
    (heFbar_const : ∀ z : AlgebraicClosure ℚ, eFbar (algebraMap (AlgebraicClosure ℚ) M.Fbar z) =
      baseToFunctionField (pullback.snd w.πX s) z)
    (heFbar_germ : ∀ (U : w.X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme ((pullback.fst w.πX s) ⁻¹ᵁ U))] (t : Γ(w.X, U)),
      eFbar (M.toBar (w.eF.symm (w.X.germToFunctionField U t))) =
        (pullback w.πX s).germToFunctionField ((pullback.fst w.πX s) ⁻¹ᵁ U) (((pullback.fst w.πX s).app U).hom t))

    (𝔐 : CurveModel (AlgebraicClosure ℚ) M.Fbar)
    (e : 𝔐.C ⟶ pullback (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase)
    (hcm : ∀ (U : w.X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
      [Nonempty (Scheme.Opens.toScheme ((pullback.fst w.πX s) ⁻¹ᵁ U))]
      [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U))]
      (t : Γ(w.X, U)),
      𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U) (((e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫ pullback.fst w.πX (Spec.map (CommRingCat.ofHom j))).app U).hom t)) =
        eFbar.symm ((pullback w.πX s).germToFunctionField ((pullback.fst w.πX s) ⁻¹ᵁ U) (((pullback.fst w.πX s).app U).hom t))) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ r : O, σ (i r) = i r) →
      ∀ x y : {p : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // p ≫ 𝔐.toBase = 𝟙 _},
        y.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ e ≫ pullback.fst (pullback.snd w.πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) →
        𝔐.pointEquivPlace y = M.gal σ • 𝔐.pointEquivPlace x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pointEquivPlace_eq_gal_smul_of_ringEquiv_functionField.solution
