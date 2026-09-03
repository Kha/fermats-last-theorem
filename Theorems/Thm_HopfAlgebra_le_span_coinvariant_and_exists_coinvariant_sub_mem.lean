import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_HopfAlgebra_le_span_coinvariant_and_exists_coinvariant_sub_mem

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem HopfAlgebra.le_span_coinvariant_and_exists_coinvariant_sub_mem
    {R : Type} [CommRing R] {L : Type} [CommRing L] [HopfAlgebra R L] [Module.Flat R L]
    {S : Type} [CommRing S] [Algebra R S]
    (δ : S →ₐ[R] S ⊗[R] L)
    (hcoassoc : ∀ s, (_root_.TensorProduct.assoc R S L L) (Algebra.TensorProduct.map δ (AlgHom.id R L) (δ s)) =
      Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.comulAlgHom R L) (δ s))
    (hcounit : ∀ s, Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.counitAlgHom R L) (δ s) = s ⊗ₜ[R] (1 : R))
    (q : S →ₐ[R] L) (hq : Function.Surjective q)
    (hqδ : ∀ s, Algebra.TensorProduct.map q (AlgHom.id R L) (δ s) = Coalgebra.comul (R := R) (q s))
    (M : Ideal S) (hM : RingHom.ker q * M = ⊥)
    (hMδ : ∀ m ∈ M, δ m ∈ M.map (algebraMap S (S ⊗[R] L))) :
    M ≤ Ideal.span {m : S | m ∈ M ∧ δ m = m ⊗ₜ[R] (1 : L)} ∧
    ∀ m ∈ M, ∃ m₀ : S, m₀ ∈ M ∧ δ m₀ = m₀ ⊗ₜ[R] (1 : L) ∧
      m - m₀ ∈ RingHom.ker (((Bialgebra.counitAlgHom R L).comp q : S →ₐ[R] R) : S →+* R) * M := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_le_span_coinvariant_and_exists_coinvariant_sub_mem.solution
