import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_eq_coaction_sub_tmul_one_of_cocycle

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem HopfAlgebra.exists_eq_coaction_sub_tmul_one_of_cocycle
    {R : Type} [CommRing R] {L : Type} [CommRing L] [HopfAlgebra R L] [Module.Flat R L]
    {S : Type} [CommRing S] [Algebra R S]
    (δ : S →ₐ[R] S ⊗[R] L)
    (hcoassoc : ∀ s, (_root_.TensorProduct.assoc R S L L) (Algebra.TensorProduct.map δ (AlgHom.id R L) (δ s)) =
      Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.comulAlgHom R L) (δ s))
    (hcounit : ∀ s, Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.counitAlgHom R L) (δ s) = s ⊗ₜ[R] (1 : R))
    (q : S →ₐ[R] L) (hq : Function.Surjective q)
    (hqδ : ∀ s, Algebra.TensorProduct.map q (AlgHom.id R L) (δ s) = Coalgebra.comul (R := R) (q s))
    (M : Ideal S) (hM : RingHom.ker q * M = ⊥)
    (hMδ : ∀ m ∈ M, δ m ∈ M.map (algebraMap S (S ⊗[R] L)))
    (e : S ⊗[R] L) (he : e ∈ M.map (algebraMap S (S ⊗[R] L)))
    (hcoc : Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.comulAlgHom R L) e =
      (_root_.TensorProduct.assoc R S L L) (Algebra.TensorProduct.map δ (AlgHom.id R L) e) +
      (_root_.TensorProduct.assoc R S L L) (e ⊗ₜ[R] (1 : L))) :
    ∃ m : S, m ∈ M ∧ e = δ m - m ⊗ₜ[R] (1 : L) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_eq_coaction_sub_tmul_one_of_cocycle.solution
