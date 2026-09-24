## Make things opaque
One of the first things to check if proofs are becoming slow, or proof terms become large, is whether [the things that should be opaque](../Opaqueness.md), are opaque.
However, note that properly managing opaqueness/transparency saves at most one or two minutes per definition. If a definition is very slow, then it is most likely related to unification. Also, make sure to properly split your definitions. By having everything split up in multiple identifiers, unification becomes a bit nicer, because computation gets blocked more.

## Try to pinpoint the origin of slowness
Sometimes, the problem is related to slow unification or normalization. If you finished the proof, but `Qed` takes ages, we want to find out which statement is the cause of this slowness. If you have not finished your proof yet, but it becomes increasingly slow, `Qed` will probably still be very slow when you are finished. To pinpoint the cause of the slowness, add the best Coq function ever:
```
Definition TODO { A : UU } : A.
Admitted.
```
Now add `apply TODO.` at the first line of the proof, and comment out the rest of the proof. See how long `Time Qed.` takes. Now, if `Time Qed.` is very fast, move the line with `TODO` down a bit. If it is slow, move `TODO` up. In this way, you can pinpoint where the slowness of `Qed` comes from.

## Remove the source of slowness
Now, some pointers for speeding up your proof:
 * `exact` has more predictable unification behavior than `apply`.
 * Both `simpl` and `cbn` can lead to weird stuff with unification in the end. If something is slow, then they are the first candidates to look at.
 * `rewrite` is slower than `refine` and `exact`, because `rewrite` creates larger proof terms.

If the problem is caused by `simpl` or `cbn`. You can opt to remove those completely. This means that you probably cannot use `rewrite`, but instead, you must do the equational reasoning by hand.

To write the correct `refine` statements to replace a `rewrite` statement (if eyeballing it does not work), here is a rough step-by-step guide (see also [this zulip conversation](https://unimath.zulipchat.com/#narrow/stream/322787-Help-needed-when-working-with-UniMath.2FCoq/topic/Slow.20proof/near/392677315) that inspired this wiki page):
 1. Work in an `etrans`. This helps, because you have only one half of the goal to worry about.
 1. Try to find the right place (where you wanted to do a rewrite) with `apply eqtohomot.` and `apply maponpaths` (and potentially `apply maponpaths_2`, `maponpaths_3` et cetera).
 1. Use the identifier that you first used with `rewrite`.

If the second step does not work, try having a look at the unfolded goal.
 * Copy it somewhere where you can edit it.
 * Remove the uninteresting parts.
 * Try to find out what the types of the different parts are (and what coercions would be applied then).
 * Try to construct an `exact (maponpaths (λ z, ... z ...) (rewrite_term)).` from this.

As a rule of thumb (not as a law), functions with transport might fail because they don't have enough type information. In that case, you need to provide them some hints, and you can do so, by (partially) filling in the implicit arguments that relate to the type and the type family.
