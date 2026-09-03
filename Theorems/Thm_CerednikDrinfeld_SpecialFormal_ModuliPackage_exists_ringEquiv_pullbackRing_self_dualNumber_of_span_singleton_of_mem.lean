import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem

set_option autoImplicit false

open CerednikDrinfeld.SpecialFormal.ModuliPackage in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem
    {O : Type} [CommRing O] {k : Type} [Field k]
    {B B' : Type} [CommRing B] [CommRing B'] (ψ' : O →+* B')
    (φ : B' →+* B) (hφ : Function.Surjective φ)
    (ρ' : B' →+* k) (hρ' : Function.Surjective ρ')
    (t : B') (ht : t ≠ 0) (hker : RingHom.ker φ = Ideal.span {t}) (htm : t ∈ RingHom.ker ρ')
    (hann : ∀ m ∈ RingHom.ker ρ', m * t = 0)
    (hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) = ρ'.comp ψ') :
    ∃ e : pullbackRing φ φ ≃+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom,
      (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom).comp e.toRingHom = pullbackFst φ φ ∧
      e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
        pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm ∧
      ((pullbackSnd φ φ).comp e.symm.toRingHom).comp
        (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) = ψ' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem.solution
