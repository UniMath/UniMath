(*

Category finite subsets of an hset

X : HSET
X', X'' : X -> hProp

where carrier(X') = { x : X | X'(x) }
and isfinite(carrier(X'))

Morphisms are inclusions: X' --> X'' given by implication: forall (x : X), X'(x) -> X''(x)

This type is a proposition


Idea for proving that this category is saturated:

idtoiso : (X1,p1) = (X2,p2) -> (X1,p1) ~= (X2,p2)

p := (X1,p1) = (X2,p2) ~ (X1 = X1) 
                       ~ (forall x, X1(x) <-> X2(x))
                       ~ (X1 ~= X2)
                       ~ (X1,p1) ~= (X2,p2)


By isweqhomot we need to prove that idtoiso =1 p, by J we should get the result

*)