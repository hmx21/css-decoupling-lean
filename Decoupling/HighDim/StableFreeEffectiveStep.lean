import Decoupling.HighDim.StableFreeEffectiveBlocks

/-!
# Explicit embedded-state update for one Schanuel step

After the first quotient lifting problem, the base modules are actual
syzygies embedded in the preceding known free terms. The next equivalence
and its inverse therefore have the displayed matrix formulas in the two
computed lift matrices U,V. No additional representation lift or projective
basis selection is needed between recursive stages.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix CategoryTheory
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

structure FiniteEmbedding (M : ModuleCat.{u} R) where
  size : ℕ
  embed : M →ₗ[R] Power R size
  injective : Function.Injective embed

namespace FiniteEmbedding
variable {M P F : ModuleCat.{u} R}

def kernel (a : ℕ) (c : F ≃ₗ[R] Power R a) (f : F →ₗ[R] M) :
    FiniteEmbedding (ModuleCat.of R (LinearMap.ker f)) where
  size := a
  embed := c.toLinearMap.comp (LinearMap.ker f).subtype
  injective := c.injective.comp (LinearMap.ker f).injective_subtype

def paired (m : FiniteEmbedding M) (p : FiniteRetract P) :
    (M × P) →ₗ[R] Power R (m.size+p.size) :=
  (powerAdd m.size p.size).toLinearMap.comp (m.embed.prodMap p.embed)

@[simp] theorem paired_apply (m : FiniteEmbedding M) (p : FiniteRetract P) (x : M × P) :
    m.paired p x = powerAdd m.size p.size (m.embed x.1,p.embed x.2) := rfl

theorem paired_injective (m : FiniteEmbedding M) (p : FiniteRetract P) :
    Function.Injective (m.paired p) := by
  intro x y h
  have h' := (powerAdd m.size p.size).injective h
  exact Prod.ext (m.injective (congrArg Prod.fst h')) (p.embed_injective (congrArg Prod.snd h'))

end FiniteEmbedding

/-- The real equivalence is retained, with explicit ambient matrix extensions
for both directions. The base modules need not be projective. -/
structure EmbeddedEquiv {M N P Q : ModuleCat.{u} R}
    (m : FiniteEmbedding M) (n : FiniteEmbedding N)
    (p : FiniteRetract P) (q : FiniteRetract Q) where
  equiv : (M × P) ≃ₗ[R] (N × Q)
  forward : Matrix (Fin (n.size+q.size)) (Fin (m.size+p.size)) R
  inverse : Matrix (Fin (m.size+p.size)) (Fin (n.size+q.size)) R
  forward_eq : ∀ x, forward *ᵥ m.paired p x = n.paired q (equiv x)
  inverse_eq : ∀ x, inverse *ᵥ n.paired q x = m.paired p (equiv.symm x)

/-- Ambient formula for the forward map, using only U,V and fixed blocks. -/
def stepForward (a b p q : ℕ)
    (U : Matrix (Fin (a+p)) (Fin (b+q)) R) (V : Matrix (Fin (b+q)) (Fin (a+p)) R) :
    Matrix (Fin (b+(a+p))) (Fin (a+(b+q))) R :=
  let A := columnBlocks (includeFirst a p) U
  let L := V*A-columnBlocks (0 : Matrix (Fin (b+q)) (Fin a) R) 1
  rowBlocks (firstRows (a := b) (b := q) L) A

/-- Ambient formula for the inverse map; the minus sign is essential. -/
def stepInverse (a b p q : ℕ)
    (U : Matrix (Fin (a+p)) (Fin (b+q)) R) (V : Matrix (Fin (b+q)) (Fin (a+p)) R) :
    Matrix (Fin (a+(b+q))) (Fin (b+(a+p))) R :=
  let B := columnBlocks (-includeFirst b q) V
  let L := columnBlocks (0 : Matrix (Fin (a+p)) (Fin b) R) 1-U*B
  rowBlocks (firstRows (a := a) (b := p) L) B

theorem stepForward_mulVec (a b p q : ℕ)
    (U : Matrix (Fin (a+p)) (Fin (b+q)) R) (V : Matrix (Fin (b+q)) (Fin (a+p)) R)
    (x : Power R a) (y : Power R (b+q)) :
    stepForward a b p q U V *ᵥ powerAdd a (b+q) (x,y) =
      powerAdd b (a+p)
        (((powerAdd b q).symm (V *ᵥ (includeFirst a p *ᵥ x+U *ᵥ y)-y)).1,
          includeFirst a p *ᵥ x+U *ᵥ y) := by
  rw [stepForward,rowBlocks_mulVec,firstRows_mulVec,Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec,columnBlocks_mulVec,columnBlocks_mulVec,
    Matrix.zero_mulVec,Matrix.one_mulVec,zero_add]

theorem stepInverse_mulVec (a b p q : ℕ)
    (U : Matrix (Fin (a+p)) (Fin (b+q)) R) (V : Matrix (Fin (b+q)) (Fin (a+p)) R)
    (x : Power R b) (y : Power R (a+p)) :
    stepInverse a b p q U V *ᵥ powerAdd b (a+p) (x,y) =
      powerAdd a (b+q)
        (((powerAdd a p).symm (y-U *ᵥ ((-includeFirst b q) *ᵥ x+V *ᵥ y))).1,
          (-includeFirst b q) *ᵥ x+V *ᵥ y) := by
  rw [stepInverse,rowBlocks_mulVec,firstRows_mulVec,Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec,columnBlocks_mulVec,columnBlocks_mulVec,
    Matrix.zero_mulVec,Matrix.one_mulVec,zero_add]

section Schanuel
variable {M N P Q F G : ModuleCat.{u} R}
  (f : F →ₗ[R] M) (g : G →ₗ[R] N) (e : (M × P) ≃ₗ[R] (N × Q))

abbrev stageLeft := f.prodMap (LinearMap.id : P →ₗ[R] P)
abbrev stageRight := e.symm.toLinearMap.comp (g.prodMap (LinearMap.id : Q →ₗ[R] Q))

/-- The exact generalized-Schanuel equivalence defined from the two actual lifts. -/
def stepEquiv (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f) :
    (LinearMap.ker f × (G × Q)) ≃ₗ[R] (LinearMap.ker g × (F × P)) :=
  ((Schanuel.kerProdEquiv (P := P) f).symm.prodCongr (LinearEquiv.refl _ _)).trans
    ((Schanuel.equivOfLifts (stageLeft f) (stageRight g e) u v hu hv).trans
      (((Schanuel.kerPostcompEquiv _ e.symm).trans (Schanuel.kerProdEquiv g)).prodCongr
        (LinearEquiv.refl _ _)))

@[simp] theorem stepEquiv_fst (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker f × (G × Q)) :
    ((stepEquiv f g e u v hu hv x).1 : G) = (v ((x.1.val,0)+u x.2)-x.2).1 := rfl

@[simp] theorem stepEquiv_snd (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker f × (G × Q)) :
    (stepEquiv f g e u v hu hv x).2 = (x.1.val,0)+u x.2 := rfl

@[simp] theorem stepEquiv_symm_fst (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker g × (F × P)) :
    ((stepEquiv f g e u v hu hv).symm x).1.val = (x.2-u (v x.2-(x.1.val,0))).1 := rfl

@[simp] theorem stepEquiv_symm_snd (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker g × (F × P)) :
    ((stepEquiv f g e u v hu hv).symm x).2 = v x.2-(x.1.val,0) := rfl

/-- The forward update formula represents the actual Schanuel map on the
actual syzygies, not merely a map on unrelated free vector spaces. -/
theorem step_forward_coordinates (a b : ℕ)
    (cF : F ≃ₗ[R] Power R a) (cG : G ≃ₗ[R] Power R b)
    (p : FiniteRetract P) (q : FiniteRetract Q)
    (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker f × (G × Q)) :
    let S := (FiniteRetract.ofCoordinates a cF).prod p
    let T := (FiniteRetract.ofCoordinates b cG).prod q
    stepForward a b p.size q.size (T.mapMatrix S u) (S.mapMatrix T v) *ᵥ
      (FiniteEmbedding.kernel a cF f).paired T x =
        (FiniteEmbedding.kernel b cG g).paired S (stepEquiv f g e u v hu hv x) := by
  let S := (FiniteRetract.ofCoordinates a cF).prod p
  let T := (FiniteRetract.ofCoordinates b cG).prod q
  have hin (z : F) : includeFirst a p.size *ᵥ cF z = S.embed (z,0) := by
    rw [includeFirst_mulVec]
    change powerAdd a p.size (cF z,0) = powerAdd a p.size (cF z,p.embed 0)
    rw [map_zero]
  have hA : (includeFirst a p.size *ᵥ cF x.1.val : Power R S.size) +
      T.mapMatrix S u *ᵥ T.embed x.2 = S.embed ((x.1.val,0)+u x.2) := by
    rw [hin,FiniteRetract.mapMatrix_mulVec,T.project_embed,map_add]
  have hL (z : F × P) : S.mapMatrix T v *ᵥ S.embed z-T.embed x.2 = T.embed (v z-x.2) := by
    rw [FiniteRetract.mapMatrix_mulVec,S.project_embed,map_sub]
  change stepForward a b p.size q.size (T.mapMatrix S u) (S.mapMatrix T v) *ᵥ
    powerAdd a (b+q.size) (cF x.1.val,T.embed x.2) =
      powerAdd b (a+p.size) (cG (v ((x.1.val,0)+u x.2)-x.2).1,S.embed ((x.1.val,0)+u x.2))
  rw [stepForward_mulVec,hA,hL,product_embed_first]

/-- The inverse update retains the genuine subtraction signs in every
characteristic. -/
theorem step_inverse_coordinates (a b : ℕ)
    (cF : F ≃ₗ[R] Power R a) (cG : G ≃ₗ[R] Power R b)
    (p : FiniteRetract P) (q : FiniteRetract Q)
    (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f)
    (x : LinearMap.ker g × (F × P)) :
    let S := (FiniteRetract.ofCoordinates a cF).prod p
    let T := (FiniteRetract.ofCoordinates b cG).prod q
    stepInverse a b p.size q.size (T.mapMatrix S u) (S.mapMatrix T v) *ᵥ
      (FiniteEmbedding.kernel b cG g).paired S x =
        (FiniteEmbedding.kernel a cF f).paired T ((stepEquiv f g e u v hu hv).symm x) := by
  let S := (FiniteRetract.ofCoordinates a cF).prod p
  let T := (FiniteRetract.ofCoordinates b cG).prod q
  have hin (z : G) : includeFirst b q.size *ᵥ cG z = T.embed (z,0) := by
    rw [includeFirst_mulVec]
    change powerAdd b q.size (cG z,0) = powerAdd b q.size (cG z,q.embed 0)
    rw [map_zero]
  have hB : ((-includeFirst b q.size) *ᵥ cG x.1.val : Power R T.size) +
      S.mapMatrix T v *ᵥ S.embed x.2 = T.embed (v x.2-(x.1.val,0)) := by
    rw [Matrix.neg_mulVec,hin,FiniteRetract.mapMatrix_mulVec,S.project_embed,map_sub]
    abel
  have hL (z : G × Q) : S.embed x.2-T.mapMatrix S u *ᵥ T.embed z = S.embed (x.2-u z) := by
    rw [FiniteRetract.mapMatrix_mulVec,T.project_embed,map_sub]
  change stepInverse a b p.size q.size (T.mapMatrix S u) (S.mapMatrix T v) *ᵥ
    powerAdd b (a+p.size) (cG x.1.val,S.embed x.2) =
      powerAdd a (b+q.size) (cF (x.2-u (v x.2-(x.1.val,0))).1,T.embed (v x.2-(x.1.val,0)))
  rw [stepInverse_mulVec,hB,hL,product_embed_first]

/-- The next represented state is constructed by the explicit matrix
formulas from the actual two solved lifts. -/
def representedStep (a b : ℕ)
    (cF : F ≃ₗ[R] Power R a) (cG : G ≃ₗ[R] Power R b)
    (p : FiniteRetract P) (q : FiniteRetract Q)
    (u : (G × Q) →ₗ[R] (F × P)) (v : (F × P) →ₗ[R] (G × Q))
    (hu : (stageLeft f).comp u = stageRight g e)
    (hv : (stageRight g e).comp v = stageLeft f) :
    EmbeddedEquiv (FiniteEmbedding.kernel a cF f) (FiniteEmbedding.kernel b cG g)
      ((FiniteRetract.ofCoordinates b cG).prod q) ((FiniteRetract.ofCoordinates a cF).prod p) where
  equiv := stepEquiv f g e u v hu hv
  forward := stepForward a b p.size q.size
    (((FiniteRetract.ofCoordinates b cG).prod q).mapMatrix ((FiniteRetract.ofCoordinates a cF).prod p) u)
    (((FiniteRetract.ofCoordinates a cF).prod p).mapMatrix ((FiniteRetract.ofCoordinates b cG).prod q) v)
  inverse := stepInverse a b p.size q.size
    (((FiniteRetract.ofCoordinates b cG).prod q).mapMatrix ((FiniteRetract.ofCoordinates a cF).prod p) u)
    (((FiniteRetract.ofCoordinates a cF).prod p).mapMatrix ((FiniteRetract.ofCoordinates b cG).prod q) v)
  forward_eq := step_forward_coordinates f g e a b cF cG p q u v hu hv
  inverse_eq := step_inverse_coordinates f g e a b cF cG p q u v hu hv

end Schanuel
end
end Decoupling.HighDim.StableFree.Effective
