import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily

set_option autoImplicit false

open CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage

universe u

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (Fobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type u)
    (Fmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Fobj B ψ hB → Fobj B' ψ' hB')
    (Fmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Fobj B ψ hB),
      Fmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Fmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Fobj B ψ hB),
      Fmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Fmap hB' hB'' g hg (Fmap hB hB' f hf x))

    (hF : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Fobj B' ψ' hB') (x'' : Fobj B'' ψ'' hB''),
        Fmap hB' hB φ' hφ' x' = Fmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Fobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Fmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Fmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (k : Type) [Field k]
    {B B' : Type} [CommRing B] [CommRing B'] [IsLocalRing B'] [IsArtinianRing B'] [IsLocalRing B] [IsArtinianRing B]
    (ψ' : O →+* B') (hB' : IsNilpotent (p : B'))
    (φ : B' →+* B) (hφ : Function.Surjective φ) (hφnil : IsNilpotent (RingHom.ker φ)) (hB : IsNilpotent (p : B))
    (ρ' : B' →+* k) (hρ' : Function.Surjective ρ') (hρ'nil : IsNilpotent (RingHom.ker ρ'))
    (hk : IsNilpotent (p : k)) (hkε : IsNilpotent (p : DualNumber k))

    (hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) = ρ'.comp ψ')
    (hP : IsNilpotent (p : pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hQ : IsNilpotent (p : pullbackRing φ φ))

    (e : pullbackRing φ φ ≃+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
    (he₁ : (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom).comp e.toRingHom = pullbackFst φ φ)
    (heStr : e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
      pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm)
    (hsnd : ((pullbackSnd φ φ).comp e.symm.toRingHom).comp
      (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) = ψ')
    (x₀' : Fobj B' ψ' hB') :
    let P := pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom
    let ψP := pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm
    let x := Fmap hB' hB φ rfl x₀'
    let xbar := Fmap hB' hk ρ' rfl x₀'
    let Rel : Fobj B' ψ' hB' → Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε → Prop :=
      fun x' τ => ∃ w : Fobj P ψP hP,
        Fmap hP hB' (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
          (pullbackFst_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = x₀' ∧
        Fmap hP hB' ((pullbackSnd φ φ).comp e.symm.toRingHom) hsnd w = x' ∧
        Fmap hP hkε (pullbackSnd ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
          (pullbackSnd_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = τ
    (∀ x' : Fobj B' ψ' hB', Fmap hB' hB φ rfl x' = x →
        ∃! τ : Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε,
          Fmap hkε hk (TrivSqZeroExt.fstHom k k k).toRingHom hfst τ = xbar ∧ Rel x' τ) ∧
    (∀ τ : Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε,
        Fmap hkε hk (TrivSqZeroExt.fstHom k k k).toRingHom hfst τ = xbar →
        ∃! x' : Fobj B' ψ' hB', Fmap hB' hB φ rfl x' = x ∧ Rel x' τ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily.solution
