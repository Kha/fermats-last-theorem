import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import P2M.Util
import P2M.Sol.S_HopfAlgebra_FVect_exists_profile_of_isFCompatible

universe u v

theorem HopfAlgebra.FVect.exists_profile_of_isFCompatible
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [CharZero R']
    (p r : ℕ) [Fact p.Prime] [NeZero r]
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R') - 1))
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    (B : Type v) [CommRing B] [HopfAlgebra R' B] [Module.Finite R' B] [Module.Free R' B]
    (hrank : Module.finrank R' B = p ^ r)
    (act : F → (B →ₐc[R'] B))
    (act_one : act 1 = BialgHom.id R' B)
    (act_mul : ∀ a b, act (a * b) = (act a).comp (act b))
    (act_add : ∀ a b, ((act (a + b) : B →ₐ[R'] B).toLinearMap) =
      LinearMap.mul' R' B ∘ₗ TensorProduct.map (act a : B →ₐ[R'] B).toLinearMap (act b : B →ₐ[R'] B).toLinearMap
        ∘ₗ Coalgebra.comul)
    (X : Fin r → B) (δ : Fin r → R')
    (h1 : ∀ i (l : Fˣ), (act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i)
    (h2 : ∀ i, X i ^ p = δ i • X (i + 1))
    (b : Module.Basis (Fin r → Fin p) R' B) (hb : ∀ d, b d = ∏ i, X i ^ (d i : ℕ))
    (h4 : ∀ i, δ i ∣ (p : R'))
    (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
    (B' : Type v) [CommRing B'] [HopfAlgebra R' B'] [Module.Finite R' B'] [Module.Free R' B']
    (hrank' : Module.finrank R' B' = p ^ r)
    (act' : F → (B' →ₐc[R'] B'))
    (act_one' : act' 1 = BialgHom.id R' B')
    (act_mul' : ∀ a b, act' (a * b) = (act' a).comp (act' b))
    (act_add' : ∀ a b, ((act' (a + b) : B' →ₐ[R'] B').toLinearMap) =
      LinearMap.mul' R' B' ∘ₗ TensorProduct.map (act' a : B' →ₐ[R'] B').toLinearMap (act' b : B' →ₐ[R'] B').toLinearMap
        ∘ₗ Coalgebra.comul)
    (X' : Fin r → B') (δ' : Fin r → R')
    (h1' : ∀ i (l : Fˣ), (act' l) (X' i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X' i)
    (h2' : ∀ i, X' i ^ p = δ' i • X' (i + 1))
    (b' : Module.Basis (Fin r → Fin p) R' B') (hb' : ∀ d, b' d = ∏ i, X' i ^ (d i : ℕ))
    (h4' : ∀ i, δ' i ∣ (p : R'))
    (h5' : ∀ i, Coalgebra.counit (R := R') (X' i) = 0)
    (u : B →ₐc[R'] B')
    (hu : ∀ l : F, u.comp (act l) = (act' l).comp u)
    (hu_inj : Function.Injective u) :
    ∃ a : Fin r → ℤ, (∀ i, 0 ≤ a i) ∧
      (∀ i, ((IsDiscreteValuationRing.addVal R' (δ i)).toNat : ℤ) =
        p * a i + ((IsDiscreteValuationRing.addVal R' (δ' i)).toNat : ℤ) - a (i + 1)) ∧
      (Function.Bijective u ↔ ∀ i, a i = 0) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_FVect_exists_profile_of_isFCompatible.solution
