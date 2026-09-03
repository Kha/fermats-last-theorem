import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m)

    (B : Type) [CommRing B] [HopfAlgebra ↥A B] [Module.Finite ↥A B] [Module.Flat ↥A B]

    (i : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A B))) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))

    (hcl : IsClosedImmersion i.1)

    (hmul : ∀ (χ χ' : WithConv (B →ₐ[↥A] AlgebraicClosure ℚ))
      (x x' xx' : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      x.1 = Spec.map (CommRingCat.ofHom (χ.ofConv : B →+* AlgebraicClosure ℚ)) ≫ i.1 →
      x'.1 = Spec.map (CommRingCat.ofHom (χ'.ofConv : B →+* AlgebraicClosure ℚ)) ≫ i.1 →
      xx'.1 = Spec.map (CommRingCat.ofHom ((χ * χ').ofConv : B →+* AlgebraicClosure ℚ)) ≫ i.1 →
      xx' = (O.L.baseChange Λ.σA).mul (barPt A) x x')

    (hpts : ∀ y : JH M H, y ∈ O.toricPts m ↔
      ∃ χ : B →ₐ[↥A] AlgebraicClosure ℚ,
        (O.pts y).1 = Spec.map (CommRingCat.ofHom (χ : B →+* AlgebraicClosure ℚ)) ≫ i.1 ≫ pullback.fst O.g Λ.σA) :
    ∃ e : B ≃ₐc[↥A] AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m),

      Spec.map (CommRingCat.ofHom ((e.symm : AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m) →ₐc[↥A] B) :
          AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m) →+* B)) ≫ (O.toricLift m hm).1 = i.1 ∧

      ∀ (m' : ℕ) (hm' : 0 < m') (hmm' : m ∣ m')
        (B' : Type) [CommRing B'] [Bialgebra ↥A B'] (e' : B' ≃ₐc[↥A] AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m'))
        (D : Type) [CommRing D] [Algebra ↥A D] (j : Spec (CommRingCat.of D) ⟶ pullback O.g Λ.σA) [Mono j]
        (a : D →ₐ[↥A] B) (a' : D →ₐ[↥A] B'),
        Spec.map (CommRingCat.ofHom (a : D →+* B)) ≫ j = i.1 →
        Spec.map (CommRingCat.ofHom (a' : D →+* B')) ≫ j =
          Spec.map (CommRingCat.ofHom ((e'.symm : AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m') →ₐc[↥A] B') :
            AddMonoidAlgebra ↥A (Fin O.toricRank → ZMod m') →+* B')) ≫ (O.toricLift m' hm').1 →
        ∀ z : D, e (a z) =
          AddMonoidAlgebra.mapDomainBialgHom ↥A
            (AddMonoidHom.pi fun k : Fin O.toricRank =>
              ((ZMod.castHom hmm' (ZMod m)).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ => ZMod m') k)))
            (e' (a' z)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff.solution
