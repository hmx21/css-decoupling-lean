import Decoupling.HighDim.ExtValuesTensorTable
import Decoupling.HighDim.MinimalLatticeYonedaContraction

/-!
# Signed contractions on the literal coefficient-tensor resolution

HD010, Appendix B.3. The operators below act on the actual modules
`K_q ⊗[K] B`. Their cocycle identities are proved from the signed Koszul
anticommutation identity. No chain-map identity is an input.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers ExtValuesTensor CochainComplex.HomComplex
open scoped TensorProduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}

/-- Tensoring a genuine Laurent-linear map with a coefficient-linear map. -/
def tensorMap {B A : ModuleCat (Laurent K D)} {q r : ℕ}
    (f : Term (Laurent K D) D q →ₗ[Laurent K D] Term (Laurent K D) D r)
    (g : Layers.coefficients B →ₗ[K] Layers.coefficients A) :
    TensorTerm B q →ₗ[Laurent K D] TensorTerm A r :=
  TensorProduct.AlgebraTensorModule.map f g

@[simp] theorem tensorMap_tmul {B A : ModuleCat (Laurent K D)} {q r : ℕ}
    (f : Term (Laurent K D) D q →ₗ[Laurent K D] Term (Laurent K D) D r)
    (g : Layers.coefficients B →ₗ[K] Layers.coefficients A)
    (v : Term (Laurent K D) D q) (b : Layers.coefficients B) :
    tensorMap f g (v ⊗ₜ[K] b) = f v ⊗ₜ[K] g b := rfl

variable (B : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]

abbrev resolution (hB : AugmentationAction B) := tensorResolution B hB
abbrev complex (hB : AugmentationAction B) := (resolution B hB).cochainComplex

def direction (a : Fin D) (q : ℕ) :
    (tensorComplex B).X (q + 1) ⟶ (tensorComplex B).X q :=
  ModuleCat.ofHom (tensorMap (boundary (Laurent K D) (Pi.single a 1) q).hom
    (LinearMap.id : Layers.coefficients B →ₗ[K] Layers.coefficients B))

@[simp] theorem direction_tmul (a : Fin D) (q : ℕ)
    (v : Term (Laurent K D) D (q + 1)) (b : Layers.coefficients B) :
    direction B a q (v ⊗ₜ[K] b) =
      (boundary (Laurent K D) (Pi.single a 1) q v) ⊗ₜ[K] b := rfl

theorem direction_anticommute (a : Fin D) (q : ℕ) :
    (tensorComplex B).d (q + 2) (q + 1) ≫ direction B a q +
      direction B a (q + 1) ≫ (tensorComplex B).d (q + 1) q = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp_all only [map_add]
  | tmul v b =>
    change direction B a q ((tensorComplex B).d (q + 2) (q + 1) (v ⊗ₜ[K] b)) +
      (tensorComplex B).d (q + 1) q (direction B a (q + 1) (v ⊗ₜ[K] b)) = 0
    rw [tensorComplex_d_tmul, direction_tmul, direction_tmul, tensorComplex_d_tmul,
      ← TensorProduct.add_tmul]
    have h := congrArg (fun f : ModuleCat.of (Laurent K D) (Term (Laurent K D) D (q + 2)) ⟶
      ModuleCat.of (Laurent K D) (Term (Laurent K D) D q) => f v)
      (YonedaDetection.boundary_anticommute (Laurent K D) (Pi.single a 1) (difference K) q)
    change boundary (Laurent K D) (Pi.single a 1) q
        (boundary (Laurent K D) (difference K) (q + 1) v) +
      boundary (Laurent K D) (difference K) q
        (boundary (Laurent K D) (Pi.single a 1) (q + 1) v) = 0 at h
    rw [h, TensorProduct.zero_tmul]

variable (hB : AugmentationAction B)

def directionCochain (a : Fin D) : Cochain (complex B hB) (complex B hB) 1 :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    ((resolution B hB).cochainComplexXIso p ((-q).toNat + 1) (by omega)).hom ≫
      direction B a (-q).toNat ≫
        ((resolution B hB).cochainComplexXIso q (-q).toNat (by omega)).inv
    else 0)

theorem directionCochain_v (a : Fin D) (q : ℕ) :
    (directionCochain B hB a).v (-(q + 1 : ℕ)) (-(q : ℤ)) (by omega) =
      ((resolution B hB).cochainComplexXIso (-(q + 1 : ℕ)) (q + 1) rfl).hom ≫
        direction B a q ≫ ((resolution B hB).cochainComplexXIso (-(q : ℤ)) q rfl).inv := by
  dsimp only [directionCochain, Cochain.mk_v]
  simp only [show (-(q : ℤ)) ≤ 0 by omega, dite_true]
  have he (p r : ℤ) (i j : ℕ) (hi : -(i : ℤ) = r) (hj : -(j : ℤ) = r)
      (hip : -((i + 1 : ℕ) : ℤ) = p) (hjp : -((j + 1 : ℕ) : ℤ) = p) :
      ((resolution B hB).cochainComplexXIso p (i + 1) hip).hom ≫ direction B a i ≫
        ((resolution B hB).cochainComplexXIso r i hi).inv =
      ((resolution B hB).cochainComplexXIso p (j + 1) hjp).hom ≫ direction B a j ≫
        ((resolution B hB).cochainComplexXIso r j hj).inv := by
    have : i = j := by omega
    subst j
    rfl
  exact he _ _ _ _ _ _ _ _

theorem directionCochain_cocycle (a : Fin D) : δ 1 2 (directionCochain B hB a) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -q)
    have hqn : q = -(n : ℤ) := by omega
    have hpn : p = -((n + 2 : ℕ) : ℤ) := by omega
    subst p
    subst q
    rw [δ_v 1 2 rfl _ _ _ _ (-(n + 1 : ℕ)) (-(n + 1 : ℕ)) (by omega) (by omega),
      directionCochain_v, directionCochain_v,
      (resolution B hB).cochainComplex_d _ _ (n + 1) n rfl rfl,
      (resolution B hB).cochainComplex_d _ _ (n + 2) (n + 1) rfl rfl]
    simp only [Cochain.zero_v, show (2 : ℤ).negOnePow = 1 from rfl,
      one_smul, Category.assoc, Iso.inv_hom_id_assoc]
    have he := congrArg (fun f =>
      ((resolution B hB).cochainComplexXIso (-((n + 2 : ℕ) : ℤ)) (n + 2) rfl).hom ≫ f ≫
        ((resolution B hB).cochainComplexXIso (-(n : ℤ)) n rfl).inv)
      (direction_anticommute B a n)
    simpa only [comp_add, add_comp, Category.assoc, comp_zero, zero_comp, add_comm, Nat.add_assoc, resolution, tensorResolution] using he
  · exact ((complex B hB).isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def directionCocycle (a : Fin D) : Cocycle (complex B hB) (complex B hB) 1 :=
  Cocycle.mk (directionCochain B hB a) 2 rfl (directionCochain_cocycle B hB a)

/-- Composition of actual homogeneous cocycles, with its differential proved. -/
def composeCocycle {C : Type*} [Category* C] [Preadditive C]
    {X Y Z : CochainComplex C ℤ} {a b c : ℤ}
    (f : Cocycle X Y a) (g : Cocycle Y Z b) (h : a + b = c) : Cocycle X Z c :=
  Cocycle.mk ((f : Cochain X Y a).comp (g : Cochain Y Z b) h) (c + 1) rfl (by
    rw [δ_comp _ _ h (a + 1) (b + 1) (c + 1) rfl rfl rfl]
    simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero])

/-- Contract the directions of an ordered cell in increasing order. This
normalization evaluates to +1 on that same unit cell. -/
def cellCocycle : (n : ℕ) → Cell D n → Cocycle (complex B hB) (complex B hB) (n : ℤ)
  | 0, _ => Cocycle.ofHom (𝟙 _)
  | n + 1, I => composeCocycle (directionCocycle B hB (I 0))
      (cellCocycle n (face I 0)) (by omega)

end
end Decoupling.HighDim.KoszulContraction
