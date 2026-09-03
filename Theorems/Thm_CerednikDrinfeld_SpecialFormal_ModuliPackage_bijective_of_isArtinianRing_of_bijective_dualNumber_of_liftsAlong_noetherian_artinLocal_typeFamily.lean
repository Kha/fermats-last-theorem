import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily

set_option autoImplicit false

universe u v

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (k : Type) [Field k] [CharP k p]

    (Gobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type u)
    (Gmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Gobj B ψ hB → Gobj B' ψ' hB')
    (Gmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Gobj B ψ hB),
      Gmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Gmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Gobj B ψ hB),
      Gmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Gmap hB' hB'' g hg (Gmap hB hB' f hf x))
    (Hobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type v)
    (Hmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Hobj B ψ hB → Hobj B' ψ' hB')
    (Hmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Hobj B ψ hB),
      Hmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Hmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Hobj B ψ hB),
      Hmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Hmap hB' hB'' g hg (Hmap hB hB' f hf x))
    (ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Gobj B ψ hB → Hobj B ψ hB)
    (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (f : B →+* B') (hf : f.comp ψ = ψ') (x : Gobj B ψ hB),
      ξ B' ψ' hB' (Gmap hB hB' f hf x) = Hmap hB hB' f hf (ξ B ψ hB x))

    (hG : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Gobj B' ψ' hB') (x'' : Gobj B'' ψ'' hB''),
        Gmap hB' hB φ' hφ' x' = Gmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Gobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Gmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Gmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hH : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Hobj B' ψ' hB') (x'' : Hobj B'' ψ'' hB''),
        Hmap hB' hB φ' hφ' x' = Hmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Hobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Hmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Hmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hlift : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_hφs : Function.Surjective φ)
      (_hφ2 : RingHom.ker φ * RingHom.ker φ = ⊥) (x : Gobj B ψ hB),
      (∃ y' : Hobj B' ψ' hB', Hmap hB' hB φ hφ y' = ξ B ψ hB x) → ∃ x' : Gobj B' ψ' hB', Gmap hB' hB φ hφ x' = x)

    (hpt : ∀ (ψk : O →+* k) (hk : IsNilpotent (p : k)), Function.Bijective (ξ k ψk hk))

    (htan : ∀ (ψk : O →+* k) (hkε : IsNilpotent (p : DualNumber k)),
      Function.Bijective (ξ (DualNumber k) ((algebraMap k (DualNumber k)).comp ψk) hkε))

    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (ρ : B →+* k) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = IsLocalRing.maximalIdeal B) :
    Function.Bijective (ξ B ψ hB) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily.solution
