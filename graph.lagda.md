# Formalization of [Algebraic Graphs with Class](https://dl.acm.org/doi/10.1145/3122955.3122956)

```
module graph where

open import Function

open import Data.List
open import Data.List.Properties using (++-identityʳ)
open import Data.Bool
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

```
infixl 4 _≈_
infixl 4 _≲_
infixl 8 _+_
infixl 9 _⇀_
```

```
data Graph (A : Set) : Set where
  ε : Graph A
  Vertex : A → Graph A
  _+_ : Graph A → Graph A → Graph A
  _⇀_ : Graph A → Graph A → Graph A
```

- `Empty` is the empty graph
- `Vertex` is the singleton graph
- `Overlay` takes the union of the vertices and edges of 2 graphs
- `Connect` overlay + create edges between all the vertices in the 2 graphs

```
data _∈ᵥ_ { A : Set } : A → Graph A → Set where
  x∈Vx : ∀ { x : A } → x ∈ᵥ Vertex x
  +ₗ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ G → x ∈ᵥ (G + H)
  +ᵣ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ H → x ∈ᵥ (G + H)
  ⇀ₗ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ G → x ∈ᵥ (G ⇀ H)
  ⇀ᵣ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ H → x ∈ᵥ (G ⇀ H)

data ⟦_,_⟧∈ₑ_ { A : Set } : A → A → Graph A → Set where
  +ₗ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ (G + H)
  +ᵣ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ (G + H)
  ⇀ₗ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ (G ⇀ H)
  ⇀ᵣ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ (G ⇀ H)
  ⇀ₗᵣ : ∀ { x y : A } { G H : Graph A } → x ∈ᵥ G → y ∈ᵥ H → ⟦ x , y ⟧∈ₑ (G ⇀ H)

record _≈_ { A : Set } ( G H : Graph A ) : Set where
  field
    vₗ : ∀ { x : A } → x ∈ᵥ G → x ∈ᵥ H
    vᵣ : ∀ { x : A } → x ∈ᵥ H → x ∈ᵥ G
    eₗ : ∀ { x y : A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ H
    eᵣ : ∀ { x y : A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ G

record _≲_ { A : Set } ( G H : Graph A ) : Set where
  field
    vₗ : ∀ { x : A } → x ∈ᵥ G → x ∈ᵥ H
    eₗ : ∀ { x y : A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ H
```

Two graphs are equal if:

- Vertex x in G iff x in H
- Edge (x, y) in G iff (x, y) in H

A graph is a subgraph if:

- Vertex x in H if x in G
- Edge (x, y) in H if (x, y) in G

```
≈→≲ : ∀ { A : Set } { G H : Graph A } → G ≈ H → G ≲ H
≈→≲ x = record { vₗ = _≈_.vₗ x ; eₗ = _≈_.eₗ x }

≈-comm : ∀ { A : Set } { G H : Graph A } → G ≈ H → H ≈ G
≈-comm x = record { vₗ = _≈_.vᵣ x ; vᵣ = _≈_.vₗ x ; eₗ = _≈_.eᵣ x ; eᵣ = _≈_.eₗ x }

≈-trans : ∀ { A : Set } { G H I : Graph A } → G ≈ H → H ≈ I → G ≈ I
≈-trans G≈H H≈I = record
                    { vₗ = λ z → _≈_.vₗ H≈I (_≈_.vₗ G≈H z)
                    ; vᵣ = λ z → _≈_.vᵣ G≈H (_≈_.vᵣ H≈I z)
                    ; eₗ = λ z → _≈_.eₗ H≈I (_≈_.eₗ G≈H z)
                    ; eᵣ = λ z → _≈_.eᵣ G≈H (_≈_.eᵣ H≈I z)
                    }

≈-refl : ∀ { A : Set } { G : Graph A } → G ≈ G
≈-refl = record
           { vₗ = λ z → z
           ; vᵣ = λ z → z
           ; eₗ = λ z → z
           ; eᵣ = λ z → z
           }
```

```
≲-trans : ∀ { A : Set } { G H I : Graph A } → G ≲ H → H ≲ I → G ≲ I
≲-trans G≲H H≲I = record
                    { vₗ = λ z → _≲_.vₗ H≲I (_≲_.vₗ G≲H z)
                    ; eₗ = λ z → _≲_.eₗ H≲I (_≲_.eₗ G≲H z)
                    }

≲-refl : ∀ { A : Set } { G : Graph A } → G ≲ G
≲-refl = record
           { vₗ = λ z → z
           ; eₗ = λ z → z
           }
```

```
+≲⇀ : ∀ { A : Set } { G H : Graph A } → G + H ≲ G ⇀ H
+≲⇀ = record
        { vₗ = λ { (+ₗ x) → ⇀ₗ x ; (+ᵣ x) → ⇀ᵣ x }
        ; eₗ = λ { (+ₗ x) → ⇀ₗ x ; (+ᵣ x) → ⇀ᵣ x }
        }
```

```
module ≈-Reasoning { A : Set } where

  infix 1 begin_
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_
  infix 3 _∎

  begin_ : ∀ { G H : Graph A } → G ≈ H → G ≈ H
  begin G≈H = G≈H

  _≈⟨⟩_ : ∀ (G : Graph A) { H : Graph A } → G ≈ H → G ≈ H
  G ≈⟨⟩ G≈H = G≈H

  _≈⟨_⟩_ : ∀ (G : Graph A) { H I : Graph A } → G ≈ H → H ≈ I → G ≈ I
  G ≈⟨ G≈H ⟩ H≈I = ≈-trans G≈H H≈I

  _∎ : ∀ (G : Graph A) → G ≈ G
  G ∎ = ≈-refl
```

```
module ≲-Reasoning { A : Set } where

  infix 1 begin_
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_ _≲⟨⟩_ _≲⟨_⟩_
  infix 3 _∎

  begin_ : ∀ { G H : Graph A } → G ≲ H → G ≲ H
  begin G≲H = G≲H

  _≈⟨⟩_ : ∀ (G : Graph A) { H : Graph A } → G ≲ H → G ≲ H
  G ≈⟨⟩ G≲H = G≲H

  _≈⟨_⟩_ : ∀ (G : Graph A) { H I : Graph A } → G ≈ H → H ≈ I → G ≲ I
  G ≈⟨ G≈H ⟩ H≈I = ≈→≲ (≈-trans G≈H H≈I)

  _≲⟨⟩_ : ∀ (G : Graph A) { H : Graph A } → G ≲ H → G ≲ H
  G ≲⟨⟩ G≲H = G≲H

  _≲⟨_⟩_ : ∀ (G : Graph A) { H I : Graph A } → G ≲ H → H ≲ I → G ≲ I
  G ≲⟨ G≲H ⟩ H≲I = ≲-trans G≲H H≲I

  _∎ : ∀ (G : Graph A) → G ≲ G
  G ∎ = ≲-refl
```

```
+-comm : ∀ { A : Set } { G H : Graph A } → G + H ≈ H + G
+-comm = record
  { vₗ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; vᵣ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; eₗ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; eᵣ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  }

+-assoc : ∀ { A : Set } { G H I : Graph A } → G + (H + I) ≈ (G + H) + I
+-assoc = record
  { vₗ = λ { (+ₗ x) → +ₗ (+ₗ x) ; (+ᵣ (+ₗ x)) → +ₗ (+ᵣ x) ; (+ᵣ (+ᵣ x)) → +ᵣ x }
  ; vᵣ = λ { (+ₗ (+ₗ x)) → +ₗ x ; (+ₗ (+ᵣ x)) → +ᵣ (+ₗ x) ; (+ᵣ x) → +ᵣ (+ᵣ x) }
  ; eₗ = λ { (+ₗ x) → +ₗ (+ₗ x) ; (+ᵣ (+ₗ x)) → +ₗ (+ᵣ x) ; (+ᵣ (+ᵣ x)) → +ᵣ x }
  ; eᵣ = λ { (+ₗ (+ₗ x)) → +ₗ x ; (+ₗ (+ᵣ x)) → +ᵣ (+ₗ x) ; (+ᵣ x) → +ᵣ (+ᵣ x) }
  }
  
+-identˡ : ∀ { A : Set } { G : Graph A } → G + ε ≈ G
+-identˡ = record
  { vₗ = λ { (+ₗ x) → x }
  ; vᵣ = λ x → +ₗ x
  ; eₗ = λ { (+ₗ x) → x }
  ; eᵣ = +ₗ 
  }

+-identʳ : ∀ { A : Set } { G : Graph A } → ε + G ≈ G
+-identʳ = record
  { vₗ = λ { (+ᵣ x) → x }
  ; vᵣ = +ᵣ
  ; eₗ = λ { (+ᵣ x) → x }
  ; eᵣ = +ᵣ
  }

+-congˡ : ∀ { A : Set } { G H I : Graph A } → G ≈ H → G + I ≈ H + I
+-congˡ G≈H = record
               { vₗ = λ { (+ₗ x) → +ₗ (_≈_.vₗ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; vᵣ = λ { (+ₗ x) → +ₗ (_≈_.vᵣ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; eₗ = λ { (+ₗ x) → +ₗ (_≈_.eₗ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; eᵣ = λ { (+ₗ x) → +ₗ (_≈_.eᵣ G≈H x) ; (+ᵣ x) → +ᵣ x }
               }

+-congʳ : ∀ { A : Set } { G H I : Graph A } → H ≈ I → G + H ≈ G + I
+-congʳ G≈H = record
               { vₗ = λ { (+ₗ x) → +ₗ x ; (+ᵣ x) → +ᵣ (_≈_.vₗ G≈H x) }
               ; vᵣ = λ { (+ₗ x) → +ₗ x ; (+ᵣ x) → +ᵣ (_≈_.vᵣ G≈H x) }
               ; eₗ = λ { (+ₗ x) → +ₗ x ; (+ᵣ x) → +ᵣ (_≈_.eₗ G≈H x) }
               ; eᵣ = λ { (+ₗ x) → +ₗ x ; (+ᵣ x) → +ᵣ (_≈_.eᵣ G≈H x) }
               }
```

+ is commutative, associative and ε is an identity element.

```
⇀-assoc : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H ⇀ I) ≈ (G ⇀ H) ⇀ I
⇀-assoc = record
  { vₗ = λ { (⇀ₗ x) → ⇀ₗ (⇀ₗ x) ; (⇀ᵣ (⇀ₗ x)) → ⇀ₗ (⇀ᵣ x) ; (⇀ᵣ (⇀ᵣ x)) → ⇀ᵣ x }
  ; vᵣ = λ { (⇀ₗ (⇀ₗ x)) → ⇀ₗ x ; (⇀ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (⇀ᵣ x) → ⇀ᵣ (⇀ᵣ x) }
  ; eₗ = λ { (⇀ₗ x) → ⇀ₗ (⇀ₗ x) ; (⇀ᵣ (⇀ₗ x)) → ⇀ₗ (⇀ᵣ x) ; (⇀ᵣ (⇀ᵣ x)) → ⇀ᵣ x ; (⇀ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (⇀ᵣ x) x₁ ; (⇀ₗᵣ x (⇀ₗ x₁)) → ⇀ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (⇀ᵣ x₁)) → ⇀ₗᵣ (⇀ₗ x) x₁ }
  ; eᵣ = λ { (⇀ₗ (⇀ₗ x)) → ⇀ₗ x ; (⇀ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (⇀ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (⇀ₗ x₁) ; (⇀ᵣ x) → ⇀ᵣ (⇀ᵣ x) ; (⇀ₗᵣ (⇀ₗ x) x₁) → ⇀ₗᵣ x (⇀ᵣ x₁) ; (⇀ₗᵣ (⇀ᵣ x) x₁) → ⇀ᵣ (⇀ₗᵣ x x₁) }
  }
 
⇀-identˡ : ∀ { A : Set } { G : Graph A } → G ⇀ ε ≈ G
⇀-identˡ = record
  { vₗ = λ { (⇀ₗ x) → x }
  ; vᵣ = ⇀ₗ
  ; eₗ = λ { (⇀ₗ x) → x }
  ; eᵣ = ⇀ₗ
  }

⇀-identʳ : ∀ { A : Set } { G : Graph A } → ε ⇀ G ≈ G
⇀-identʳ = record
  { vₗ = λ { (⇀ᵣ x) → x }
  ; vᵣ = ⇀ᵣ
  ; eₗ = λ { (⇀ᵣ x) → x }
  ; eᵣ = ⇀ᵣ
  }

⇀-congˡ : ∀ { A : Set } { G H I : Graph A } → G ≈ H → G ⇀ I ≈ H ⇀ I
⇀-congˡ G≈H = record
               { vₗ = λ { (⇀ₗ x) → ⇀ₗ (_≈_.vₗ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x }
               ; vᵣ = λ { (⇀ₗ x) → ⇀ₗ (_≈_.vᵣ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x }
               ; eₗ = λ { (⇀ₗ x) → ⇀ₗ (_≈_.eₗ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ (_≈_.vₗ G≈H x) x₁ }
               ; eᵣ = λ { (⇀ₗ x) → ⇀ₗ (_≈_.eᵣ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ (_≈_.vᵣ G≈H x) x₁ }
               }

⇀-congʳ : ∀ { A : Set } { G H I : Graph A } → H ≈ I → G ⇀ H ≈ G ⇀ I
⇀-congʳ G≈H = record
               { vₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≈_.vₗ G≈H x) }
               ; vᵣ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≈_.vᵣ G≈H x) }
               ; eₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≈_.eₗ G≈H x) ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ x (_≈_.vₗ G≈H x₁) }
               ; eᵣ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≈_.eᵣ G≈H x) ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ x (_≈_.vᵣ G≈H x₁) }
               }

⇀-congˡ-≲ : ∀ { A : Set } { G H I : Graph A } → G ≲ H → G ⇀ I ≲ H ⇀ I
⇀-congˡ-≲ G≲H = record
                 { vₗ = λ { (⇀ₗ x) → ⇀ₗ (_≲_.vₗ G≲H x) ; (⇀ᵣ x) → ⇀ᵣ x }
                 ; eₗ = λ { (⇀ₗ x) → ⇀ₗ (_≲_.eₗ G≲H x) ; (⇀ᵣ x) → ⇀ᵣ x ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ (_≲_.vₗ G≲H x) x₁ }
                 }

⇀-congʳ-≲ : ∀ { A : Set } { G H I : Graph A } → H ≲ I → G ⇀ H ≲ G ⇀ I
⇀-congʳ-≲ H≲I = record
                 { vₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≲_.vₗ H≲I x) }
                 ; eₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≲_.eₗ H≲I x) ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ x (_≲_.vₗ H≲I x₁) }
                 }
```

⇀ is associative and ε is an identity element

```
⇀+-dist : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H + I) ≈ G ⇀ H + G ⇀ I
⇀+-dist = record
            { vₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ (+ₗ x)) → +ₗ (⇀ᵣ x) ; (⇀ᵣ (+ᵣ x)) → +ᵣ (⇀ᵣ x) }
            ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (+ₗ x) ; (+ᵣ (⇀ₗ x)) → ⇀ₗ x ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ (+ᵣ x) }
            ; eₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ (+ₗ x)) → +ₗ (⇀ᵣ x) ; (⇀ᵣ (+ᵣ x)) → +ᵣ (⇀ᵣ x) ; (⇀ₗᵣ x (+ₗ x₁)) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (+ᵣ x₁)) → +ᵣ (⇀ₗᵣ x x₁) }
            ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (+ₗ x) ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (+ₗ x₁) ; (+ᵣ (⇀ₗ x)) → ⇀ₗ x ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ (+ᵣ x) ; (+ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (+ᵣ x₁) }
            }

+⇀-dist : ∀ { A : Set } { G H I : Graph A } → (G + H) ⇀ I ≈ G ⇀ I + H ⇀ I
+⇀-dist = record
            { vₗ = λ { (⇀ₗ (+ₗ x)) → +ₗ (⇀ₗ x) ; (⇀ₗ (+ᵣ x)) → +ᵣ (⇀ₗ x) ; (⇀ᵣ x) → +ₗ (⇀ᵣ x) }
            ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ (+ₗ x) ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ x ; (+ᵣ (⇀ₗ x)) → ⇀ₗ (+ᵣ x) ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ x }
            ; eₗ = λ { (⇀ₗ (+ₗ x)) → +ₗ (⇀ₗ x) ; (⇀ₗ (+ᵣ x)) → +ᵣ (⇀ₗ x) ; (⇀ᵣ x) → +ₗ (⇀ᵣ x) ; (⇀ₗᵣ (+ₗ x) x₁) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ (+ᵣ x) x₁) → +ᵣ (⇀ₗᵣ x x₁) }
            ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ (+ₗ x) ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ x ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (+ₗ x) x₁ ; (+ᵣ (⇀ₗ x)) → ⇀ₗ (+ᵣ x) ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ x ; (+ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (+ᵣ x) x₁ }
            }

⇀-decomp : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H ⇀ I) ≈ G ⇀ H + (G ⇀ I + H ⇀ I)
⇀-decomp = record
             { vₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ x) → +ᵣ (+ᵣ x) }
             ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (+ᵣ (+ₗ (⇀ₗ x))) → ⇀ₗ x ; (+ᵣ (+ₗ (⇀ᵣ x))) → ⇀ᵣ (⇀ᵣ x) ; (+ᵣ (+ᵣ x)) → ⇀ᵣ x }
             ; eₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ x) → +ᵣ (+ᵣ x) ; (⇀ₗᵣ x (⇀ₗ x₁)) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (⇀ᵣ x₁)) → +ᵣ (+ₗ (⇀ₗᵣ x x₁)) }
             ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (⇀ₗ x₁) ; (+ᵣ (+ₗ (⇀ₗ x))) → ⇀ₗ x ; (+ᵣ (+ₗ (⇀ᵣ x))) → ⇀ᵣ (⇀ᵣ x) ; (+ᵣ (+ₗ (⇀ₗᵣ x x₁))) → ⇀ₗᵣ x (⇀ᵣ x₁) ; (+ᵣ (+ᵣ x)) → ⇀ᵣ x }
             }
```

```
+-congʳ-alt : ∀ { A : Set } { G H I : Graph A } → H ≈ I → G + H ≈ G + I
+-congʳ-alt {_} {G} {H} {I} H≈I =
  begin
    G + H
  ≈⟨ +-comm ⟩
    H + G
  ≈⟨ +-congˡ H≈I ⟩
    I + G
  ≈⟨ +-comm ⟩
    G + I
  ∎
  where open ≈-Reasoning

+-idem : ∀ { A : Set } { G : Graph A } → G + G ≈ G
+-idem {_} {G} =
  begin
    G + G
  ≈⟨ ≈-comm ⇀-identˡ ⟩
    (G + G) ⇀ ε
  ≈⟨ +⇀-dist ⟩
    (G ⇀ ε) + (G ⇀ ε)
  ≈⟨ ≈-comm +-identˡ ⟩
    ((G ⇀ ε) + (G ⇀ ε)) + ε
  ≈⟨ ≈-comm (+-congʳ ⇀-identˡ) ⟩
    ((G ⇀ ε) + (G ⇀ ε)) + (ε ⇀ ε)
  ≈⟨ ≈-comm +-assoc ⟩
    (G ⇀ ε) + ((G ⇀ ε) + (ε ⇀ ε))
  ≈⟨ ≈-comm ⇀-decomp ⟩
    G ⇀ (ε ⇀ ε)
  ≈⟨ ⇀-assoc ⟩
    (G ⇀ ε) ⇀ ε
  ≈⟨ ⇀-identˡ ⟩
    G ⇀ ε
  ≈⟨ ⇀-identˡ ⟩
    G
  ∎
  where open ≈-Reasoning

+-absorp : ∀ { A : Set } { G H : Graph A } → G ⇀ H + G + H ≈ G ⇀ H
+-absorp {_} {G} {H} =
  begin
    G ⇀ H + G + H
  ≈⟨ +-congˡ (+-congʳ (≈-comm ⇀-identˡ)) ⟩
    G ⇀ H + G ⇀ ε + H
  ≈⟨ +-congʳ (≈-comm ⇀-identˡ) ⟩
    G ⇀ H + G ⇀ ε + H ⇀ ε
  ≈⟨ ≈-comm +-assoc ⟩
    G ⇀ H + (G ⇀ ε + H ⇀ ε)
  ≈⟨ ≈-comm ⇀-decomp ⟩
    G ⇀ (H ⇀ ε)
  ≈⟨ ⇀-congʳ ⇀-identˡ ⟩
    G ⇀ H
  ∎
  where open ≈-Reasoning

⇀-sat : ∀ { A : Set } { G : Graph A } → G ⇀ G ⇀ G ≈ G ⇀ G
⇀-sat {_} {G} =
  begin
    G ⇀ G ⇀ G
  ≈⟨ ≈-comm ⇀-assoc ⟩
    G ⇀ (G ⇀ G)
  ≈⟨ ⇀-decomp ⟩
    G ⇀ G + (G ⇀ G + G ⇀ G)
  ≈⟨ +-congʳ +-idem ⟩
    G ⇀ G + G ⇀ G
  ≈⟨ +-idem ⟩
    G ⇀ G
  ∎
  where open ≈-Reasoning
```

```
ε-noedge : ∀ { A : Set } { x y : A } → ¬ (⟦ x , y ⟧∈ₑ ε)
ε-noedge = λ ()
```

```
edge : {A : Set} → A → A → Graph A
edge x y = (Vertex x) ⇀ (Vertex y)

vertices : {A : Set} → List A → Graph A
vertices = (foldr _+_ ε) ∘ (map Vertex)

clique : {A : Set} → List A → Graph A
clique = (foldr _⇀_ ε) ∘ (map Vertex)
```

```
vertices[x]=Vx : { A : Set } → ∀ { x : A } → vertices [ x ] ≈ Vertex x
vertices[x]=Vx {_} {x} =
  begin
    vertices [ x ]
  ≈⟨⟩
    Vertex x + ε
  ≈⟨ +-identˡ ⟩
    Vertex x
  ∎
  where open ≈-Reasoning


edgexy=clique[x,y] : { A : Set } → ∀ { x y : A } → (edge x y) ≈ (clique (x ∷ (y ∷ [])))
edgexy=clique[x,y] {_} {x} {y} =
  begin
    edge x y
  ≈⟨⟩
    Vertex x ⇀ Vertex y
  ≈⟨ ≈-comm ⇀-identˡ ⟩
    (Vertex x ⇀ Vertex y) ⇀ ε
  ≈⟨ ≈-comm ⇀-assoc ⟩
    Vertex x ⇀ (Vertex y ⇀ ε)
  ≈⟨⟩
    clique (x ∷ (y ∷ []))
  ∎
  where open ≈-Reasoning


vertices-∈ᵥ-∷ : { A : Set } → ∀ { x : A } ( y : A ) { xs : List A } → x ∈ᵥ vertices xs → x ∈ᵥ vertices (y ∷ xs)
vertices-∈ᵥ-∷ y x∈xs = +ᵣ x∈xs

clique≲clique∷ : { A : Set } → ∀ ( xs : List A ) ( x : A ) → (clique xs) ≲ (clique (x ∷ xs))
clique≲clique∷ xs x = record
  { vₗ = ⇀ᵣ
  ; eₗ = ⇀ᵣ
  }

vertices≲clique : { A : Set } → ∀ ( xs : List A ) → (vertices xs) ≲ (clique xs)
vertices≲clique [] =
  begin
    vertices []
  ≈⟨⟩
    clique []
  ∎
  where open ≲-Reasoning
vertices≲clique (x ∷ xs) =
  begin
    vertices (x ∷ xs)
  ≲⟨⟩
    Vertex x + vertices xs
  ≲⟨ +≲⇀ ⟩
    Vertex x ⇀ vertices xs
  ≲⟨ ⇀-congʳ-≲ (vertices≲clique xs) ⟩
    Vertex x ⇀ clique xs
  ≲⟨⟩
    clique (x ∷ xs)
  ∎
  where open ≲-Reasoning

clique-++-connect : { A : Set } → ∀ ( xs ys : List A ) → clique (xs ++ ys) ≈ ((clique xs) ⇀ (clique ys))
clique-++-connect [] ys =
  begin
    clique ([] ++ ys)
  ≈⟨⟩
    clique ys
  ≈⟨ ≈-comm ⇀-identʳ ⟩
    ε ⇀ clique ys
  ≈⟨⟩
    (clique []) ⇀ (clique ys)
  ∎
  where open ≈-Reasoning
clique-++-connect (x ∷ xs) ys = 
  begin
    clique ((x ∷ xs) ++ ys)
  ≈⟨⟩
    clique (x ∷ (xs ++ ys))
  ≈⟨⟩
    Vertex x ⇀ clique (xs ++ ys)
  ≈⟨ ⇀-congʳ (clique-++-connect xs ys) ⟩
    Vertex x ⇀ (clique xs ⇀ clique ys)
  ≈⟨ ⇀-assoc ⟩
    (Vertex x ⇀ clique xs) ⇀ clique ys
  ≈⟨⟩
    clique (x ∷ xs) ⇀ clique ys
  ∎
  where open ≈-Reasoning
```

