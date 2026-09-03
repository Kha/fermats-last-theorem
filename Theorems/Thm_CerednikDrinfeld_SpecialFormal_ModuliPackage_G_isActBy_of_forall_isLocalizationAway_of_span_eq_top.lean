import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_forall_isLocalizationAway_of_span_eq_top
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr) (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : ModuliPackage.GPoint 𝒪 M B)

    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hE : E₀ e = (r : K₀) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))

    (n : ℕ) (f : Fin n → B) (hspan : Ideal.span (Set.range f) = ⊤)

    (hleg : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L],
      (algebraMap B L).comp (x'.ψ : Onr →+* B) = (algebraMap B L).comp ((frobTwist Onr Fr ((m' : ℤ) - 2 * k) x.ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (hloc : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (r : L)),
      ∃ t t' : Rigidified r Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp (x.ψ : Onr →+* B)) ∧ t'.IsAdmissible ι ((algebraMap B L).comp (x'.ψ : Onr →+* B)) ∧
        η L ((algebraMap B L).comp (x.ψ : Onr →+* B)) hL t =
          M.map (ψ' := (algebraMap B L).comp (x.ψ : Onr →+* B)) x.nilp hL (algebraMap B L) rfl x.pt ∧
        η L ((algebraMap B L).comp (x'.ψ : Onr →+* B)) hL t' =
          M.map (ψ' := (algebraMap B L).comp (x'.ψ : Onr →+* B)) x'.nilp hL (algebraMap B L) rfl x'.pt ∧
        Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries k m' ((algebraMap B L).comp (x.ψ : Onr →+* B)) t t') :
    ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top.solution
