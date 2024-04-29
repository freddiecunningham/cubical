{-# OPTIONS --cubical #-}
-- {-# OPTIONS --cubical --no-import-sorts --safe #-}

{-
CONVENTIONS:
    - Use Type ℓ for universes (so Set ℓ is not allowed in order to avoid confusion with the type of h-sets).
    - Local definitions should be put in where, let-in or private so that it is easy to see which are the main results of a file and which are just helper definitions.
    - Use copattern-matching when instantiating records for efficiency. This seems especially important when constructing Iso's.
-}
-- Module Cubical.Diss.MyGroups

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude as Prelude

open import Cubical.Foundations.Pointed.Base as Pointed

open import Cubical.Homotopy.Base as HomotopyBase

open import Cubical.Homotopy.Connected as Connected

open import Cubical.Homotopy.Loopspace as Loopspace

open import Cubical.Foundations.Transport as Transport

open import Cubical.Foundations.Path as Path

open import Cubical.Data.Sigma.Properties as Sigma

open import Cubical.Data.Sigma.Base as SigmaBase

open import Cubical.Foundations.Equiv.Base as Equiv

open import Cubical.Foundations.Equiv.Fiberwise as EquivFiber

open import Cubical.Foundations.Univalence as UnivalenceAx

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Surjection as Surjection

open import Cubical.Functions.Embedding as Embedding

open import Cubical.Functions.Image as Image

open import Cubical.HITs.Replacement.Base as ReplacementPrinciple

open import Cubical.Relation.Nullary.Base as RelationBase

open import Cubical.Relation.Nullary.Properties as RelationProperties

open import Cubical.Data.FinSet.DecidablePredicate as DecPredicate

open import Cubical.Relation.Nullary.DecidablePropositions as DecProposition

open import Cubical.HITs.Truncation as Truncation

open import Cubical.HITs.SetQuotients as SetQuotients

open import Cubical.Data.FinSet as FinSet

open import Cubical.HITs.S1 as S1

open import Cubical.Foundations.HLevels as HLevels

{-
Use 
Cubical.Data.Equality.Base/Conversion 
Path and _≡_ are equal (Path≡Eq)
conversion between dependent paths and PathP (pathOver→PathP and PathP→pathOver)
-}


private
  variable
    ℓ ℓ' : Level

-- 2. Intro to Univalent Mathematics
{-
Definition 2.5.1
    For any type X and for any a, b : X, let
        symm_{a,b} : (a ≡ b) → (b ≡ a)
    be the function defined by induction by setting symm_{a,a}(refl­ₐ) :≡ reflₐ

    sym : x ≡ y → y ≡ x
    sym p i = p (~ i)
    -# INLINE sym #-

Definition 2.5.2
    For any type X and for any a, b, c : X, let
        trans_{a,b,c} : (a ≡ b) → ((b ≡ c) → (a ≡ c))
    be the function defined by induction by setting (trans_{a,b,b}(p))(refl_{b}) :≡ p

    _∙_ : x ≡ y → y ≡ z → x ≡ z
    p ∙ q = refl ∙∙ p ∙∙ q
    
-}
open Prelude using (refl; sym; _∙_; _≡_) public
-- open Prelude renaming (sym to _⁻¹) public
{-
Definition 2.5.4
    Let X be a type, and let T(x) be a family of types parametrized by a variable x:X. 
    Suppose a,b:X and  e:a≡b. Then we may construct a function of type T(a) → T(b). The function
        trp : T(a) → T(b)

    -- transport is a special case of transp
    transport : {A B : Type ℓ} → A ≡ B → A → B
    transport p a = transp (λ i → p i) i0 a


-}
open Prelude using (transport) public
-- inverse direction
open Transport using (transport⁻) public

{-

More precisely, functions induce maps on identity types, as the following
definition makes precise. Topologically, this
corresponds to saying that every function is “continuous”, i.e. preserves paths.

Definition 2.6.1. 
    For all types X, Y, functions f: X→Y and elemenrts x,x':X, the function
        ap_{f,x,x'} : (x ≡ x') → (f(x) ≡ f(x'))
    is defined by induction by setting ap_{f,x,x}(reflₓ) :≡ refl_{f(x)}

    cong : (f : (a : A) → B a) (p : x ≡ y) →
        PathP (λ i → B (p i)) (f x) (f y)
    cong f p i = f (p i)
    -# INLINE cong #-
-}
open Prelude using (cong) public
open Prelude using (congS) public


{-
Definition 2.6.4
    Let f,g: (x : X) → (Y x) Define the function
        ptw_{f,g} : (f ≡ g) → ((x:X) → f(x) ≡ g(x))
    by induction setting ptw_{f,f}(refl_f) :≡ x ↦ refl_{f(x)}.

From HoTT book 2.9:
From a traditional perspective, this would say that two functions which are equal at each point
are equal as functions. From a topological perspective, it would say that a path in a function
space is the same as a continuous homotopy. And from a categorical perspective, it would say
that an isomorphism in a functor category is a natural family of isomorphisms.

Dependent path type. (Path over Path)
-- Introduced with lambda abstraction and eliminated with application,
-- just like function types.
-- PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
-}
open HomotopyBase using (_∼_) public
open Prelude using (PathP) public
-- open Prelude using (subst; J ; JRefl) public
-- open HomotopyBase using (funExt∼)

{-
Deinition 2.7.6
Definition 2.7.6. 
    Suppose we are given a type X, a family of types Y(x)
    parametrized by the elements x of X, and a function f : ∏ₓ Y(x). Given
    elements x, x′: X and a path p : x ≡ x, we define

    by induction on p, setting
        apd_f (reflₓ) :≡ refl_f(x).

-}
open Path using (PathP≡Path ; PathP≡Path⁻) public

{-
2.8 Sum Types / Sigma Types

    fst : (Σ_{x:X} Y(x)) → X, fst(a,b) :≡ a;
    snd(a,b) : Y(a), snd(a,b) :≡ b.
    snd : ∏_{z:Σ_{x:X} Y(X)} Y(fst(z))

    {A : I → Type ℓ} {B : (i : I) → (a : A i) → Type ℓ'}
    {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}

-}
-- Equality of Σ-types + Isomorphisms
open Sigma using (ΣPathP; ΣPath≃PathΣ) public
open SigmaBase using (∃-syntax) public


{-
Definition 2.9.1
    Given a type X, define a type isContr(X) by setting
        isContr(X) :≡ Σ_{c:X}∏_{x:X} (c ≡ x)
    If (c,h):isContr(X), then c will be called the center of the contraction h,
    and we call the type X contractible.

    isContr' : Type ℓ → Type ℓ
    isContr' A = Σ[ x ∈ A ] (∀ y → x ≡ y)

Lemma 2.9.2
    For any Type X and an element a of X, the singleton type
    Σ_{x:X}(a ≡ x) is contractible.

    isContrSingl : (a : A) → isContr (singl a)
    isContrSingl a .fst = (a , refl)
    isContrSingl a .snd p i .fst = p .snd i
    isContrSingl a .snd p i .snd j = p .snd (i ∧ j)
-}
open Prelude using (isContr; isContrSingl) public

{-
Defintion 2.9.3
Note; Cubical.Functions.Image - Image = Σ[ y ∈ B ] isInImage y:≡(∃[ x ∈ A ] f x ≡ y)

    Given a function f: X → Y and an element y:Y, the fiber
    (or preimage) f⁻¹(y) is encoded by defining
        f⁻¹(y) :≡ Σ_{x:X}(y ≡ f(x))

    In HoTT book:
    Definition 4.2.4
        The fiber of a map f: A → B over a point y:B is
            fib_{f}(y) :≡ Σ_{x:X}(f(x) ≡ y)
    
    fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
    fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

    -- the definition using Π-type
    isEquiv' : ∀ {ℓ}{ℓ'}{A : Type ℓ}{B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
    isEquiv' {B = B} f = (y : B) → isContr (fiber f y)

    _≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
    A ≃ B = Σ (A → B) \ f → (isEquiv f)
    equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
    equivFun e = fst e
    
-}

open Equiv using (fiber; isEquiv; _≃_; equivFun) public


{-
Lemma 2.9.9-16
Σ-cong-equiv : (e : A ≃ A')
             → ((x : A) → B x ≃ B' (equivFun e x))
             → Σ A B ≃ Σ A' B'
Σ-cong-equiv e e' = isoToEquiv (Σ-cong-iso (equivToIso e) (equivToIso ∘ e'))

Σ-cong' : (p : A ≡ A') → PathP (λ i → p i → Type ℓ') B B' → Σ A B ≡ Σ A' B'
Σ-cong' p p' = cong₂ (λ (A : Type _) (B : A → Type _) → Σ A B) p p'


HoTT Book 2.3
Topologically, the transportation lemma can be viewed as a “path lifting” operation in a fibration. 
We think of a type family P : A → UU as a fibration with base space A, with P(x) being
the fiber over x, and with ∑(x:A) P(x) being the total space of the fibration, with first projection
∑(x:A) (P(x)) → A.

We may also occasionally use other topological terminology when speaking about type families. 
For instance, we may refer to a dependent function f : ∏(x:A) P(x) as a section of the
fibration P, and we may say that something happens fiberwise if it happens for each P(x). For
instance, a section f : ∏(x:A) P(x) shows that P is “fiberwise inhabited”.

-}
open Sigma using (Σ-cong-equiv) public 

open EquivFiber using (fiberEquiv; totalEquiv) public

{-
Principe 2.9.17
    The axiom of function extensionality postulates that the function 
    ptw_{f,g} :(f ≡ g) → ∏_{x:X} f(x) ≡ g(x) in Definition 2.6.4 is
    an equivalence. Formally, we postulate the existence of an element
    funext : isEquiv(ptw_{f ,g}). From that we can construct the corresponding
    inverse function
        ptw⁻¹_{f,g} : (∏_{x:X} f(x) ≡ g(x)) → (f ≡ g)

    funExt' : {B : A → I → Type ℓ'} 
        {f : (x : A) → B x i0} {g : (x : A) → B x i1}
        → ((x : A) → PathP (B x) (f x) (g x))
        → PathP (λ i → (x : A) → B x i) f g
    funExt' p i x = p x i

    funExt⁻ : {B : A → I → Type ℓ'}
        {f : (x : A) → B x i0} {g : (x : A) → B x i1}   
        → PathP (λ i → (x : A) → B x i) f g
        → ((x : A) → PathP (B x) (f x) (g x))
    funExt⁻ eq x i = eq i x
-}
open Prelude using (funExt; funExt⁻)


-- 2.12.8 Unary Sums
data Copy (X : Type ℓ) : Type ℓ where
  inn : X → Copy X


-- Define the destructor
out : {X : Type ℓ} → Copy X → X
out (inn x) = x

inout : {X : Type ℓ} (z : Copy X) → inn (out z) ≡ z
inout (inn x) = refl


{-
Principle 2.13.2
    (Univalence Axiom). Let UU be a universe. Voevodsky’s
    univalence axiom for UU postulates that p ↦ p̃ is an equivalence of type
    (X ≡ Y) → (X ≃ Y), for all X,Y : UU. Formally, we postulate the
    existence of a family of elements
        ua_{X,Y} : isEquiv((p : X ≡ Y) ↦ trpᵁ_{p})
    parameterized by X,Y:UU

    -- The ua constant
    ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
    ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                       ; (i = i1) → (B , idEquiv B) })

    univalence : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
    univalence .fst = pathToEquiv
    univalence .snd = isEquivPathToEquiv

-}

open UnivalenceAx using (ua; pathToEquiv; uaβ; uaη; univalence)



{-

-- Define the equivalence function
copyEquiv : {X : Type ℓ} → Copy X ≡ X
copyEquiv = record { to   = out ; 
                     from = inn ; 
                     isInverse₁ = λ z → inout z ; 
                     isInverse₂ = λ x → refl }

-}

{-
Definition 2.15.6
isProp(P) :≡ ∏ p,q : P, (p →= q)
isSet(S) :≡ ∏ x,y : S, isProp(x →= y) ≡ ∏ x,y : S, ∏ p,q :(x →= y), (p →= q)
isGrpd(G) :≡ ∏g,h : G, isSet(g →= h) ≡ ...
-}
open Prelude using (isProp; isSet; isGroupoid)


{-
NOTE: 
(-2) = Contractible Types - Has exactlt one inhabitant up to homotopy
(-1) = Propositions - iff all its inhabitants are equal,
(0) = Groupoid types (or sets) - unique identity proofs (UIP) 
(>0) = Groups & Higher groupoids etc
Memo, a type is (n+1)-truncated if all it's path spaces are n-truncated - for n ≥ (−2)

HoTT includes operations to truncate types at any given level, 
which is useful when higher equalities are irrelevant or 
when simplifying the type's structure is desirable for theoretical or practical reasons.

Defintion 2.16.1
    Let T be a type. The propositional truncation of T is the type ||T|| defined by the following constrs
        1) an element of constructor |t| : ||T|| ∀ t : T 
            "if A is inhabited so is ||A||"
        2) an identification (path) proviiding an identification type x ≡ y ∀ x,y : ||T||
    The identification constructor ensure that ||T|| is a proposition.

Definition 2.16.2
    Let T be a type. We call T non-empty if we have an elemenet of ||T||.
    We may also say that T is inhabitied

Definition 2.16.3
    Given props P and Q, define their disjunction by (P ∨ Q) :≡ ||P ∐ Q||.
    It expresses the property that P is True or Q is True

Definition 2.16.4
    (∃_{x:X} P(x)) :≡ ||∃_{x:X} P(x)|| 
    There exists an x specfing that P is true, however x is notfiven explicity

Definition 2.16.5
    (∃!_{x:X} P(x)) :≡ isContr(∃_{x:X} P(x)) 


Proposition Truncation
    data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
    ∣_∣₁ : A → ∥ A ∥₁
    squash₁ : ∀ (x y : ∥ A ∥₁) → x ≡ y

    HoTT Book:
    Definition 3.7.1. We define traditional logical notation using truncation as follows, where P
    and Q denote mere propositions (or families thereof):
        ⊤           :≡ 𝟙
        ⊥           :≡ 𝟘
        P ∧ Q       :≡ P × Q
        P ⇒ Q      :≡ P → Q
        P ⇔ Q      :≡ P = Q
        ¬P          :≡ P → 𝟘
        P ∨ Q       :≡ ∥P + Q∥
        ∀(x:A) P(x) :≡ ∏(x:A) P(x)
        ∃(x:A) P(x) :≡ ∥Σ(x:A) P(x)∥
-}

-- propositional truncation
-- not index is off by 2
open PT using (∥_∥₁)

{- 
Definition 2.16.8 
    Let A be a type. For any element a of A, 
    the type Aₐ :≡ ∑ x : A ∥a →= x∥ is called the connected component of a in A.
    We say that elements x, y of A are in the same component of A if ∥x →= y∥.
    The type A is called connected if it is non-empty with all elements in the
    same component. Formally, this property is encoded by the following
    proposition
        isConn(A) :≡ ∥A∥ × ∏_{x,y:A} ∥x ≡ y∥
    One can view being connected as a weak form of being contractible
    without direct access to a center and to identifications of elements

    -- Note that relative to most sources, this notation is off by +2
    isConnected : ∀ {ℓ} (n : HLevel) (A : Type ℓ) → Type ℓ
    isConnected n A = isContr (hLevelTrunc n A)

    isConnectedPoint : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
        → isConnected (suc n) A
        → (a : A) → isConnectedFun n (λ(_ : Unit) → a)
    isConnectedPoint n connA a₀ a =
        isConnectedRetract n
            snd (_ ,_) (λ _ → refl)
            (isConnectedPath n connA a₀ a)

-}
open Connected using (isConnected) public
-- open Connected using (isConnected; isConnectedFun; isConnectPoint)

{-

Definition 2.17.1. 
    A function f : 𝐴 → B is a surjection, or is surjective, 
    if ∀ b : B there exists an a : A s.t. b ≡ f(a), that is, ∃_{a:A} (b ≡ f(a))
or HoTT 4.6.1
    We say f is surjective (or a surjection) if for every b : B we have ∥fib_{b}(b)∥

    isSurjection : (A → B) → Type _
    isSurjection f = ∀ b → ∥ fiber f b ∥₁

Note:
    "For clarity when dealing with types that are not sets, we will speak of embeddings instead of injections."
    Below if A & B are sets then we can say f is injective, however we should avoid this word for types that are not sets.

Definition 2.17.2. 
    A function f : A → B is an injection, or is injective, if
    f⁻¹(b) is a proposition for all b : B. The property of being an injection is
    encoded by the type isInj(f)) :≡ ∏_{b:B} isProp(f⁻¹(b)).
or
    We say f is an embedding if, 
    for every x, y : A the function ap_{f}: (x ≡ y) → (f(x) ≡ f(y)) is an equivalence

    isEmbedding : (A → B) → Type _
    isEmbedding f = ∀ w x → isEquiv {A = w ≡ x} (ap f)
Note:
    Embeddings are generalizations of injections. The usual definition of injection as:
        f x ≡ f y → x ≡ y
    is not well-behaved with higher h-levels, while embeddings are.

    In this sense
    isEmbedding→Inj
        : {f : A → B}
        → isEmbedding f
        → ∀ w x → f w ≡ f x → w ≡ x
    isEmbedding→Inj {f = f} embb w x p 
        = equiv-proof (embb w x) p .fst .fst

    isEmbedding×isSurjection→isEquiv : isEmbedding f × isSurjection f → isEquiv f 
    equiv-proof (isEmbedding×isSurjection→isEquiv {f = f} (emb , sur)) b =
        inhProp→isContr (PT.rec fib' (λ x → x) fib) fib'
        where
            hpf : hasPropFibers f
            hpf = isEmbedding→hasPropFibers emb

            fib : ∥ fiber f b ∥₁
            fib = sur b

            fib' : isProp (fiber f b)
            fib' = hpf b
-}

open Surjection using (isSurjection) public
open Embedding using (isEmbedding; isEmbedding→Inj) public

open Surjection using (isEmbedding×isSurjection→isEquiv) public


{-
Definition 2.17.11
    Let A, B be types and let f : A → B. We define the image of f as
        im(f) :≡ Σ_{y:B} ∃_{x:A} (y ≡ f x)
    Note:
    that (∃_{x:a} (y ≡ f x)) ≡ ∥f⁻¹(y)∥, the propositional truncation of the fiber. 
    im(f) is called the propositional image.

HoTT 7.6.3
    imₙ(f) :≡ ∑_{b:B} ∥ fib_{f}(b) ∥ₙ 

        isInImage : B → Type _
        isInImage y = ∃[ x ∈ A ] f x ≡ y
        
        isPropIsInImage : (x : B) → isProp (isInImage x)
        isPropIsInImage x = isPropPropTrunc

        Image : Type _
        Image = Σ[ y ∈ B ] isInImage y
    
-}

open Image using (Image; restrictToImage; isSurjectionImageRestriction; imageFactorization) public

{-
2.18 Decidability, excluded middle & propositional resizing

Defintion 2.18.1
    A proposition P is called decidable if P ∐ ¬P holds.

Priniciple 2.18.2
    (LEM) For every prop P, the prop P ∐ ¬P holds.
-}

open RelationBase using (Dec; NonEmpty; Stable)
open RelationProperties using (isPropDec; mapDec)


{-
Principle 2.19.4
    From Rijke Intro To HoTT 18.1.8
    (Replacement Axiom)
    For any universe U, we assume that for any map f : A → B from an essentially U-small type A,
    to a locally U-small type B , the image im(f) is essentially U small.

    Type-theoretic replacement: a construction taking a map F : A → B where
    - A : Type ℓA
    - B : Type ℓB,
    - the identity types of B essentially have universe level ℓ≅B,
    and producing an image of F with universe level (ℓ-max ℓA ℓ≅B).
-}

open ReplacementPrinciple using (Replacement; replacement≃Image)

{-
Predicates and Subtypes
Definition 2.20.2
    A subtype of a type T is a type S together with an injection f : S ­. T.
    Selecting a universe U as a repo for such types S,
    allows us to introduce the type of subtyoes of T in U as follows

        Subᵁ_{T} :≡ Σ_{S:U} Σ_{f:S→T} isInj(f)

Definition 2.20.10
    The type of types that are prositions and the type of types that are sets are defined as:

        Prop_{U} :≡ Σ_{X:U} isProp(X)
        
        Set_{U} :≡ Σ_{X:U} isSet(X)
    
    DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
    DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

    isSetDecProp : isSet (DecProp ℓ)
    isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropDec (P .snd)))
-}

PropU : {Type ℓ} → Type (ℓ-suc ℓ)
PropU {ℓ} = Σ  (Type ℓ) isProp

SetU : {Type ℓ} → Type (ℓ-suc ℓ)
SetU {ℓ} = Σ (Type ℓ) isSet 

open DecProposition using (isSetDecProp)

open DecPredicate using (isDecProp∃; isDecProp∀; isDecProp∀2)

{-
Theorem 2.20.12 (Hedberg)
    For any type A for which we have a function of type ∏_{x,y:A} ((x ≡ y) ∐ ¬ (x ≡ t)) is a decidable set

    Proof (Outline):
        ¬¬(x = y) → (x = y) for any x,y ∈ X then X is a set

    -- Proof of Hedberg's theorem: a type with decidable equality is an h-set
    Discrete→Separated : Discrete A → Separated A
    Discrete→Separated d x y = Dec→Stable (d x y)

    Discrete→isSet : Discrete A → isSet A
    Discrete→isSet = Separated→isSet ∘ Discrete→Separated
-}

{- 
Definition 2.21.1 
    A pointed type is a pair (A, a) where A is a type and a is an element of A. The type of pointed types is:

    Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
    Pointed ℓ = TypeWithStr ℓ (λ x → x)

    pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
    pt = str

    Pointed₀ = Pointed ℓ-zero

    -- Pointed functions 
    _→∙_ : (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
    (A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] f a ≡ b

    _→∙_∙ : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
    (A →∙ B ∙) .fst = A →∙ B
    (A →∙ B ∙) .snd .fst x = pt B
    (A →∙ B ∙) .snd .snd = refl

    idfun∙ : (A : Pointed ℓ) → A →∙ A
    idfun∙ A .fst x = x
    idfun∙ A .snd = refl
    -Pointed equivalences -
    _≃∙_ : (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
    A ≃∙ B = Σ[ e ∈ fst A ≃ fst B ] fst e (pt A) ≡ pt B

    - Underlying pointed map of an equivalence -
    ≃∙map : {A : Pointed ℓ} {B : Pointed ℓ'} → A ≃∙ B → A →∙ B
    fst (≃∙map e) = fst (fst e)
    snd (≃∙map e) = snd e

-}

open Pointed using (Pointed; _→∙_; _→∙_∙; idfun∙; _≃∙_; ≃∙map) public


{-
Equivalences between truncations
-}

open Truncation using (propTrunc≃Trunc1; setTrunc≃Trunc2; groupoidTrunc≃Trunc3) public


{-
2.22.9 Set Quotients

Definition 2.22.10
    Given a type A and an equivalence relation R : A → A → Prop, 
    we define the quotient set A/R as the image of the map R : A → (A → Prop)

-}
open SetQuotients using (_/_; elimProp; elimContr; discreteSetQuotients) public

{-
2.24 Finite Sets

    Definition 2.24.1
        For any type X define succ(X) :≡ X ⨿ True. 
        Define inductively the type family Fin(n), for each  n:ℕ, by setting Fin(0) :≡ ∅
        and Fin(succ(n)) :≡ succ(Fin(n)). The type Fin(b) is called the type with n elements, 
        and we denote its elements by 0, 1, . . . , 𝑛 − 1 rather than by the corresponding expressions using inl and inr.
        We also define abbrv 𝕟 :≡ FIn(n) for a natural number n, so 𝟘 :≡ Fin(0) etc

    Definition 2.24.3
        Given a type X, we define prop
            isFinSet(X) :≡ ∃_{n:ℕ} (X ≡ 𝕟)
        to express that X is a finite set

        -- definition of (Bishop) finite sets
        -- this definition makes cardinality computation more efficient
        isFinSet : Type ℓ → Type ℓ
        isFinSet A = Σ[ n ∈ ℕ ] ∥ A ≃ Fin n ∥₁
        or
        isFinSet' : Type ℓ → Type ℓ
        isFinSet' A = ∥ Σ[ n ∈ ℕ ] A ≃ Fin n ∥₁



    Definition 2.24.5
        The groupoid of fin sets is defined by
            FinSet :≡ Σ_{S:Set} isFinSet(S)
        
        for n:ℕ, the gropoid of sets of cardinality n is
            FinSetₙ :≡ Σ_{S:Set} ∥𝕟 = S∥

    FinSet : (ℓ : Level) → Type (ℓ-suc ℓ)
    FinSet ℓ = TypeWithStr _ isFinSet

    FinProp : (ℓ : Level) → Type (ℓ-suc ℓ)
    FinProp ℓ = Σ[ P ∈ FinSet ℓ ] isProp (P .fst)

-}

open FinSet using (isFinSet; FinSet; FinProp; isGroupoidFinSet; isSetFinProp; card)


--Circle
{-
Definition 3.1.1 
    The Circle is a type of S¹:U with an constructor base and an idenfication loop.
    
    data S¹ : Type₀ where
        base : S¹
        loop : base ≡ base

Theorem 3.1.2 
    rec : ∀ {ℓ} {A : Type ℓ} (b : A) (l : b ≡ b) → S¹ → A
    rec b l base     = b
    rec b l (loop i) = l i

    -- circle induction
    elim : ∀ {ℓ} (C : S¹ → Type ℓ) (b : C base) (l : PathP (λ i → C (loop i)) b b) → (x : S¹) → C x
    elim _ b l base     = b
    elim _ b l (loop i) = l i

Lemma 3.1.6 The circle is connected

    isConnectedS¹ : (s : S¹) → ∥ base ≡ s ∥₁
    isConnectedS¹ base = ∣ refl ∣₁
    isConnectedS¹ (loop i) =
    squash₁ ∣ (λ j → loop (i ∧ j)) ∣₁ ∣ (λ j → loop (i ∨ ~ j)) ∣₁ i

-}

open S1 using (S¹; helix; ΩS¹; encode; winding; intLoop; rec; elim) public

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

{-
Definition 3.9.3

-}

-- 4. Groups
{-
Definition 4.2.1. 
    Given a pointed type X ≡ (A, a) we define its type of loops by ΩX :≡ (a ≡ a)

    -- loop space of a pointed type
    Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
    Ω (_ , a) = ((a ≡ a) , refl)
    
-}
open Loopspace using (Ω) public
open Pointed using (Pointer) public

{-
Definition 4.2.6 
    The type of a pointed, connected groupoids is the type
    Σ A : U, (A × isConn(A) × isGrpd(A)).

    Remark 4.2.8 We shall refer to pointed connected groupoid (A, a , p, q) simply by the pointed type X :≡ (A, a). 
    There is no essential difference in this, for the types isConn(A) & isGrpd(A) are propositions, & so the witnesses p and q are unique.
-}

pcgU : {Type ℓ} → Type (ℓ-suc ℓ)
pcgU {ℓ} = Σ  (Type ℓ) λ A → (A × isConnected 0 A × isGroupoid A)

open import Cubical.Data.Nat

record PointedConnectedGroupoid ℓ (k : ℕ) : Type (ℓ-suc ℓ) where
    constructor pcg
    field
        base-pt : Pointed ℓ
        isConn : isConnected (k + 1) (Type ℓ)
        isGrpd : isGroupoid (Type ℓ)


GroupΣ : {ℓ : Level} (k : ℕ) → Type (ℓ-suc ℓ)
GroupΣ {ℓ} k = Σ[ A ∈ Type ℓ ] A × (isConnected (k + 1) A) × (isGroupoid  A)

open HLevels using (isOfHLevel) public

record BGroup ℓ (n k : ℕ) : Type (ℓ-suc ℓ) where
  constructor bgroup
  field
    base-pt : Pointed ℓ
    isConn : isConnected (k + 1) (Type ℓ)
    isTrun : isOfHLevel (n + k + 2) (Type ℓ)


1BGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
1BGroup ℓ = BGroup ℓ 0 1

basetype : {ℓ : Level} {n k : ℕ} (BG : BGroup ℓ n k) → Type ℓ
basetype BG = typ (BGroup.base-pt BG)

basepoint : {ℓ : Level} {n k : ℕ} (BG : BGroup ℓ n k) → basetype BG
basepoint BG = pt (BGroup.base-pt BG)

{-
Definition 4.2.9
    The type of groups us a wrapped copy of the type of pointed connected Groupoids U¹ (by Remark 4.2.8, Pointed type),
    Group :≡ Copyₒ(U¹)
    with constructor Ω : U¹ → Group. A group is an element of Group

    The wrapped copy of X is an inductive type Copy(X) with constructor
        in : X → Copy(X)

-}




{-
Definition 4.2.11. Let 𝐺 be a group. We regard every group as a group of
symmetries, and thus we refer to the elements of ΩBG as the symmetries in
𝐺; they are the symmetries of the designated shape sh𝐺 of 𝐺. (Notice the
careful distinction between the phrases “symmetries in” and “symmetries
of ”.) We adopt the notation UG for the type ΩBG of symmetries in 𝐺; it
is a set.5

5Taking the symmetries in a group
thus defines a map U : Group → Set,
with Ω𝑋 ↦→ Ω𝑋. Just as with “B”,
we write the “U” so that it matches
the shape of its operand.

-}

{-
Definition 4.2.14. For a groupoid 𝐴 with a specified point 𝑎, we define
the automorphism group of 𝑎 : 𝐴 by
    Autₐ(a) :≡ Ω(A₍ₐ₎, (𝑎, !)),

i.e. Autₐ(a) is the group with the classifiying type BAutₐ(a) ≡ (A₍ₐ₎, (a, !)),
the connected component of A containing a, pointed at a.

-}

{-
Definition 4.2.26. 
    A group G is abelian if all symmetries commute, in the sense that the proposition

        isAb(G) :≡ ∏_{g,h:UG} gh≡hg

-}


{-
Definition 4.7.15 Actions in a type

Definition 4.7.16
    If G is any (possibly higher) group and A is any type of objects, then we define an action by G in A as a function

        X : BG → A

    The specific object of type A being acted on is X(sh_G) : A, and the actio  itself is given by a transport.
    This generalizes our earlier definition of G-sets, X : BG → Set.

Definition 4.7.17. 
The standard action of G on its designated shape sh_G is obtained by taking A :≡ BG and X :≡ id_BG

-}



-- 5. Subgroups
{-
Theorem 5.9.2 
    (Orbit-stabilizer theorem). Fix a G-type X and a point x : X(sh_G).
    There is a canonical action G̃ : BGₓ → U, acting on G̃ (sh_G) ≃ G with orbit
    type G̃_hGx ≃ 𝒪ₓ.

Proof. 
    Define G̃(x, y, !) :≡ (sh_G = x). 


Extra.
    Now supose that G is a 1-group acting on a set. We see that the orbit type is a set iff all the stabilizer groups are trivial,
    i.e. iff the action is free.
    If G is a 1-group, then so is each stabilizer-group, and in this case (of a set-action), the orbit-stabilizer theorem tells us that.
-}

{-
Theorem 5.9.3 (Lagrange’s Theorem).
If H → G is a subgroup, then H has a natural action on G, and all the orbits under this action are equivalent.

-}



{-
Lemma 5.11.1 Let G be a finite group acting on a finite set X. Then the set of orbits is finite with cardinality.
    Card(X/G) = 1/Card(G) Σ g : El G, Card(Xᵍ),
    where Xᵍ = {x : X | g x = x} is the set of elements that are fixed by g.

Proof.
    Since X & G is finite, equality is decidable on their elements. Therefore each Xᵍ is a finite set, and since G is finite,
    we can decide whether x, y are in the same orbit by searching for a g : El G with g x = y. Hence the set of orbits is finite set as well.

Extra.
    Consider now the set R :≡ ∑ g : El G. Xᵍ, and the function q : R → X defined by q(g, x) :≡ x. 
    The map q⁻1(x) → Gₓ that sends (g, x) to g is a bĳection. 
    Thus, we get the equivalences 
        R ≡ ∑ g : El G. Xᵍ ≃ ∑ x : X Gₓ ≃ ∑ z : X/G ∑ x : 𝒪ᵣ  𝐺 x ,
    where the last step writes 𝑋 as a union of orbits. Within each orbit 𝒪 , 
    the stabilizer groups are conjugate, and thus have the same finite cardinality,
    which from the orbit-stabilizer theorem (Theorem 5.9.2), is the cardinality of G divided by the cardinality of Oᵣ. 
    We conclude that Card(R) = Card(X/G) Card(G), as desired.

-}


-- Finite Groups

{-
Definition 7.2.1. 
    A finite group is a group such that the set UG is finite. If
    G is a finite group, then the cardinality |G| is the cardinality of the finite
    set UG (i.e., UG : FinSet(|G|)).

-}

{-
For finite groups, Lagrange’s Theorem 5.9.3 takes on the form of a counting argument
Lemma 7.2.3 (Lagrange’s theorem: counting version). 
        Let i : Hom(H, G) be a subgroup of a finite group G. Then
            |G| = |G/H| · |H|
        
        If |H| = |G|, then H = G (as subgroups of G).

Proof.
    Consider the H action of H on G, i.e., 
    the H-set i*G : BH → Set with i*G(x) :≡ (sh_G = Bi(x)), 
    so that G/H is just another name for the orbits i*G/H :≡ ∑ x : BH i∗G(x). 
    Note that composing with the structure identity pᵢ : sh_G = Bi(sh_H) gives an equivalence i*G(sh_H) ≃ UG, 
    so that |i*G(sh_H)| = |G|.

-}  
