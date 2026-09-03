import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeNilpotent_of_model_jZero_torsion_heckeNilpotent

theorem ModularCurve.heckeNilpotent_of_model_jZero_torsion_heckeNilpotent
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (φ' : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar M
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ' t h)) → ((e g : JZero M)) = t • (e f : JZero M))
    (Tc : H →ₐc[GaloisRep.ratLocalizedAt p] H)
    (hTc : (Tc : H →ₐ[GaloisRep.ratLocalizedAt p] H) = φ' (heckeGen ⟨p, hp.out⟩)) :
    ∃ m : ℕ, (Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) ^ m =
      Algebra.linearMap (GaloisRep.ratLocalizedAt p) H ∘ₗ Coalgebra.counit := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeNilpotent_of_model_jZero_torsion_heckeNilpotent.solution
