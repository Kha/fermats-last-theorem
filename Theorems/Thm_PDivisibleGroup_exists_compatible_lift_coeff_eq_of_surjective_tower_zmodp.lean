import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp

open scoped TensorProduct

universe u v

theorem PDivisibleGroup.exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]

    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (Et : ℕ → Type u) [∀ v, CommRing (Et v)] [∀ v, HopfAlgebra 𝓞 (Et v)] [∀ v, Module.Free 𝓞 (Et v)] [∀ v, Module.Finite 𝓞 (Et v)]
    (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v) (hst : ∀ v, Function.Surjective (st v))
    (θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] Ge v) (hθe : ∀ v, Function.Bijective (θe v))
    (hθe_comp : ∀ v, (θe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) = (se v).comp (θe (v + 1)))

    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (Ge v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (se v) (m (v + 1)) = m v) :
    ∃ ĉ : ℕ → ∀ v, Et v,
      (∀ k v, st v (ĉ k (v + 1)) = ĉ k v) ∧
      (∀ k v, Coalgebra.counit (R := 𝓞) (ĉ k v) = 0) ∧
      (∀ v, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Ge v)),
        Deformation.DieudonneModule.of (ZMod p) p (Ge v) n u = m v ∧
        (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (Ge v)).coeff ⟨n - 1 - k, by omega⟩ =
           θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v)) ∧
        (∀ k, n ≤ k → θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v) = 0)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp.solution
