import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf

set_option autoImplicit false
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (G H : CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O)
    (hGsh : G.IsZariskiSheaf) (hHsh : H.IsZariskiSheaf)
    (ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      G.obj B ψ hB → H.obj B ψ hB)
    (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (f : B →+* B') (hf : f.comp ψ = ψ') (x : G.obj B ψ hB),
      ξ B' ψ' hB' (G.map hB hB' f hf x) = H.map hB hB' f hf (ξ B ψ hB x))
    (hG : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : G.obj B' ψ' hB') (x'' : G.obj B'' ψ'' hB''),
      G.map hB' hB φ' hφ' x' = G.map hB'' hB φ'' hφ'' x'' →
      ∃! z : G.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        G.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        G.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hH : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : H.obj B' ψ' hB') (x'' : H.obj B'' ψ'' hB''),
      H.map hB' hB φ' hφ' x' = H.map hB'' hB φ'' hφ'' x'' →
      ∃! z : H.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        H.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        H.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')

    (hlift : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_hφs : Function.Surjective φ)
      (_hφ2 : RingHom.ker φ * RingHom.ker φ = ⊥) (x : G.obj B ψ hB),
      (H.fibre hB' hB φ hφ (ξ B ψ hB x)).Nonempty →
      ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : Fin n) (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
          (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
          (hL' : IsNilpotent (p : L')) (hL : IsNilpotent (p : L))
          (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp φ)
          (hφLψ : φL.comp ((algebraMap B' L').comp ψ') = (algebraMap B L).comp ψ),
          (G.fibre hL' hL φL hφLψ (G.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl x)).Nonempty)

    (hbase : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      (p : B) = 0 → Function.Bijective (ξ B ψ hB))

    (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    Function.Bijective (ξ B ψ hB) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf.solution
