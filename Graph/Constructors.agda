open import Graph.Base
open import Graph.Properties
open import Graph.Reasoning


open import Data.List
open import Function

module Graph.Constructors where

edge : {A : Set} → A → A → Graph A
edge x y = (Vertex x) ⇀ (Vertex y)

vertices : {A : Set} → List A → Graph A
vertices = (foldr _+_ ε) ∘ (map Vertex)

clique : {A : Set} → List A → Graph A
clique = (foldr _⇀_ ε) ∘ (map Vertex)

vertices[x]=Vx : { A : Set } → ∀ { x : A } → vertices [ x ] ≡ Vertex x
vertices[x]=Vx {_} {x} = begin
  vertices [ x ]  ≡⟨⟩
  Vertex x + ε    ≡⟨ +-identityʳ ⟩
  Vertex x        ∎
  where open ≡-Reasoning

edgexy=clique[x,y] : { A : Set } → ∀ { x y : A } → (edge x y) ≡ (clique (x ∷ (y ∷ [])))
edgexy=clique[x,y] {_} {x} {y} = begin
  edge x y                   ≡⟨⟩
  Vertex x ⇀ Vertex y        ≡⟨ sym ⇀-identˡ ⟩
  (Vertex x ⇀ Vertex y) ⇀ ε  ≡⟨ sym ⇀-assoc ⟩
  Vertex x ⇀ (Vertex y ⇀ ε)  ≡⟨⟩
  clique (x ∷ (y ∷ []))      ∎
  where open ≡-Reasoning

vertices≤clique : { A : Set } → ∀ ( xs : List A ) → (vertices xs) ≤ (clique xs)
vertices≤clique [] = begin ε ∎
  where open ≤-Reasoning
vertices≤clique (x ∷ xs) = begin
  vertices (x ∷ xs)      ≡⟨⟩
  Vertex x + vertices xs ≤⟨ +⇀-order ⟩
  Vertex x ⇀ vertices xs ≤⟨ ⇀-congʳ-≤ (vertices≤clique xs) ⟩
  Vertex x ⇀ clique xs   ≡⟨⟩
  clique (x ∷ xs)        ∎
  where open ≤-Reasoning

clique-++-connect : { A : Set } → ∀ ( xs ys : List A ) → clique (xs ++ ys) ≡ ((clique xs) ⇀ (clique ys))
clique-++-connect [] ys = begin
  clique ([] ++ ys)          ≡⟨⟩
  clique ys                  ≡⟨ sym ⇀-identʳ ⟩
  ε ⇀ clique ys              ≡⟨⟩
  (clique []) ⇀ (clique ys)  ∎
  where open ≡-Reasoning
clique-++-connect (x ∷ xs) ys = begin
  clique ((x ∷ xs) ++ ys)             ≡⟨⟩
  clique (x ∷ (xs ++ ys))             ≡⟨⟩
  Vertex x ⇀ clique (xs ++ ys)        ≡⟨ ⇀-congʳ (clique-++-connect xs ys) ⟩
  Vertex x ⇀ (clique xs ⇀ clique ys)  ≡⟨ ⇀-assoc ⟩
  (Vertex x ⇀ clique xs) ⇀ clique ys  ≡⟨⟩
  clique (x ∷ xs) ⇀ clique ys         ∎
  where open ≡-Reasoning
