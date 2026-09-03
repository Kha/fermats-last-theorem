import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian open AlgebraicGeometry hiding exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    (E' : FakeEllipticCurve Λ 1 B') (E'' : FakeEllipticCurve Λ 1 B'') (EB : FakeEllipticCurve Λ 1 B)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'') :
    ∃ (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ''))
      (k' : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
      (k'' : E''.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k''),
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackFst_pullbackSnd_isPushout_of_surjective_of_isNilpotent.solution
