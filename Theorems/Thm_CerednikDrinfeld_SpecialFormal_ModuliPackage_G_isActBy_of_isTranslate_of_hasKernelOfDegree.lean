import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_isTranslate_of_hasKernelOfDegree

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal
theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_isTranslate_of_hasKernelOfDegree
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr) (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)

    (hηnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hBr : IsNilpotent (r : B))
    (χ χ' : Onr →ₐ[𝒪] B) (t t' : Rigidified r Φ B)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hleg : χ' = frobTwist Onr Fr ((m' : ℤ) - 2 * k) χ)
    (ht : t.IsAdmissible ι (χ : Onr →+* B)) (ht' : t'.IsAdmissible ι (χ' : Onr →+* B))
    (hE : E₀ e = (r : K₀) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries k m' (χ : Onr →+* B) t t') :
    ModuliPackage.G.IsActBy ι Φ η Fr E₀ g
      (⟨χ, hBr, η B (χ : Onr →+* B) hBr t⟩ : ModuliPackage.GPoint 𝒪 M B) ⟨χ', hBr, η B (χ' : Onr →+* B) hBr t'⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_isTranslate_of_hasKernelOfDegree.solution
