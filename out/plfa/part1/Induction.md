---
src       : "src/plfa/part1/Induction.lagda.md"
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
---

{% raw %}<pre class="Agda"><a id="146" class="Keyword">module</a> <a id="153" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.part1.Induction</a> <a id="174" class="Keyword">where</a>
</pre>{% endraw %}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{% raw %}<pre class="Agda"><a id="769" class="Keyword">import</a> <a id="776" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="814" class="Symbol">as</a> <a id="817" class="Module">Eq</a>
<a id="820" class="Keyword">open</a> <a id="825" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="828" class="Keyword">using</a> <a id="834" class="Symbol">(</a><a id="835" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="838" class="Symbol">;</a> <a id="840" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="844" class="Symbol">;</a> <a id="846" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="850" class="Symbol">;</a> <a id="852" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="855" class="Symbol">)</a>
<a id="857" class="Keyword">open</a> <a id="862" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a><a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="890" class="Symbol">;</a> <a id="892" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="897" class="Symbol">;</a> <a id="899" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="905" class="Symbol">;</a> <a id="907" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="909" class="Symbol">)</a>
<a id="911" class="Keyword">open</a> <a id="916" class="Keyword">import</a> <a id="923" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="932" class="Keyword">using</a> <a id="938" class="Symbol">(</a><a id="939" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="940" class="Symbol">;</a> <a id="942" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="946" class="Symbol">;</a> <a id="948" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="951" class="Symbol">;</a> <a id="953" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="956" class="Symbol">;</a> <a id="958" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="961" class="Symbol">;</a> <a id="963" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="966" class="Symbol">)</a>
</pre>{% endraw %}

## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
(You do not have to prove these properties.)

Give an example of an operator that has an identity and is
associative but is not commutative.
(You do not have to prove these properties.)


## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables:
{% raw %}<pre class="Agda"><a id="3407" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#3407" class="Function">_</a> <a id="3409" class="Symbol">:</a> <a id="3411" class="Symbol">(</a><a id="3412" class="Number">3</a> <a id="3414" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3416" class="Number">4</a><a id="3417" class="Symbol">)</a> <a id="3419" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3421" class="Number">5</a> <a id="3423" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3425" class="Number">3</a> <a id="3427" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3429" class="Symbol">(</a><a id="3430" class="Number">4</a> <a id="3432" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3434" class="Number">5</a><a id="3435" class="Symbol">)</a>
<a id="3437" class="Symbol">_</a> <a id="3439" class="Symbol">=</a>
  <a id="3443" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3453" class="Symbol">(</a><a id="3454" class="Number">3</a> <a id="3456" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3458" class="Number">4</a><a id="3459" class="Symbol">)</a> <a id="3461" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3463" class="Number">5</a>
  <a id="3467" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3475" class="Number">7</a> <a id="3477" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3479" class="Number">5</a>
  <a id="3483" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3491" class="Number">12</a>
  <a id="3496" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3504" class="Number">3</a> <a id="3506" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3508" class="Number">9</a>
  <a id="3512" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3520" class="Number">3</a> <a id="3522" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3524" class="Symbol">(</a><a id="3525" class="Number">4</a> <a id="3527" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3529" class="Number">5</a><a id="3530" class="Symbol">)</a>
  <a id="3534" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:

    -- In the beginning, no properties are known.

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:

    -- On the first day, one property is known.
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:

    -- On the second day, two properties are known.
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:

    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now:

    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property:

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="7762" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="7770" class="Symbol">:</a> <a id="7772" class="Symbol">∀</a> <a id="7774" class="Symbol">(</a><a id="7775" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7775" class="Bound">m</a> <a id="7777" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7777" class="Bound">n</a> <a id="7779" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7779" class="Bound">p</a> <a id="7781" class="Symbol">:</a> <a id="7783" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7784" class="Symbol">)</a> <a id="7786" class="Symbol">→</a> <a id="7788" class="Symbol">(</a><a id="7789" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7775" class="Bound">m</a> <a id="7791" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7793" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7777" class="Bound">n</a><a id="7794" class="Symbol">)</a> <a id="7796" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7798" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7779" class="Bound">p</a> <a id="7800" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7802" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7775" class="Bound">m</a> <a id="7804" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7806" class="Symbol">(</a><a id="7807" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7777" class="Bound">n</a> <a id="7809" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7811" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7779" class="Bound">p</a><a id="7812" class="Symbol">)</a>
<a id="7814" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="7822" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7827" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7827" class="Bound">n</a> <a id="7829" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7829" class="Bound">p</a> <a id="7831" class="Symbol">=</a>
  <a id="7835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7845" class="Symbol">(</a><a id="7846" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7851" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7853" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7827" class="Bound">n</a><a id="7854" class="Symbol">)</a> <a id="7856" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7858" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7829" class="Bound">p</a>
  <a id="7862" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7870" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7827" class="Bound">n</a> <a id="7872" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7874" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7829" class="Bound">p</a>
  <a id="7878" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7886" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7891" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7893" class="Symbol">(</a><a id="7894" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7827" class="Bound">n</a> <a id="7896" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7898" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7829" class="Bound">p</a><a id="7899" class="Symbol">)</a>
  <a id="7903" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="7905" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="7913" class="Symbol">(</a><a id="7914" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7918" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a><a id="7919" class="Symbol">)</a> <a id="7921" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a> <a id="7923" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a> <a id="7925" class="Symbol">=</a>
  <a id="7929" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7939" class="Symbol">(</a><a id="7940" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7944" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="7946" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7948" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a><a id="7949" class="Symbol">)</a> <a id="7951" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7953" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a>
  <a id="7957" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7965" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7969" class="Symbol">(</a><a id="7970" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="7972" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7974" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a><a id="7975" class="Symbol">)</a> <a id="7977" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7979" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a>
  <a id="7983" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7991" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7995" class="Symbol">((</a><a id="7997" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="7999" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8001" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a><a id="8002" class="Symbol">)</a> <a id="8004" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8006" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a><a id="8007" class="Symbol">)</a>
  <a id="8011" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="8014" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="8019" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8023" class="Symbol">(</a><a id="8024" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="8032" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="8034" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a> <a id="8036" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a><a id="8037" class="Symbol">)</a> <a id="8039" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="8045" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8049" class="Symbol">(</a><a id="8050" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="8052" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8054" class="Symbol">(</a><a id="8055" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a> <a id="8057" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8059" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a><a id="8060" class="Symbol">))</a>
  <a id="8065" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="8073" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8077" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7918" class="Bound">m</a> <a id="8079" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8081" class="Symbol">(</a><a id="8082" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7921" class="Bound">n</a> <a id="8084" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8086" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7923" class="Bound">p</a><a id="8087" class="Symbol">)</a>
  <a id="8091" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="11115" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11115" class="Function">+-assoc-2</a> <a id="11125" class="Symbol">:</a> <a id="11127" class="Symbol">∀</a> <a id="11129" class="Symbol">(</a><a id="11130" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11130" class="Bound">n</a> <a id="11132" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11132" class="Bound">p</a> <a id="11134" class="Symbol">:</a> <a id="11136" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11137" class="Symbol">)</a> <a id="11139" class="Symbol">→</a> <a id="11141" class="Symbol">(</a><a id="11142" class="Number">2</a> <a id="11144" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11146" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11130" class="Bound">n</a><a id="11147" class="Symbol">)</a> <a id="11149" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11151" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11132" class="Bound">p</a> <a id="11153" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11155" class="Number">2</a> <a id="11157" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11159" class="Symbol">(</a><a id="11160" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11130" class="Bound">n</a> <a id="11162" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11164" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11132" class="Bound">p</a><a id="11165" class="Symbol">)</a>
<a id="11167" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11115" class="Function">+-assoc-2</a> <a id="11177" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a> <a id="11179" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a> <a id="11181" class="Symbol">=</a>
  <a id="11185" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11195" class="Symbol">(</a><a id="11196" class="Number">2</a> <a id="11198" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11200" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a><a id="11201" class="Symbol">)</a> <a id="11203" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11205" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a>
  <a id="11209" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11217" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11221" class="Symbol">(</a><a id="11222" class="Number">1</a> <a id="11224" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11226" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a><a id="11227" class="Symbol">)</a> <a id="11229" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11231" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a>
  <a id="11235" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11243" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11247" class="Symbol">((</a><a id="11249" class="Number">1</a> <a id="11251" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11253" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a><a id="11254" class="Symbol">)</a> <a id="11256" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11258" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a><a id="11259" class="Symbol">)</a>
  <a id="11263" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11266" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11271" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11275" class="Symbol">(</a><a id="11276" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11351" class="Function">+-assoc-1</a> <a id="11286" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a> <a id="11288" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a><a id="11289" class="Symbol">)</a> <a id="11291" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11297" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11301" class="Symbol">(</a><a id="11302" class="Number">1</a> <a id="11304" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11306" class="Symbol">(</a><a id="11307" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a> <a id="11309" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11311" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a><a id="11312" class="Symbol">))</a>
  <a id="11317" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11325" class="Number">2</a> <a id="11327" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11329" class="Symbol">(</a><a id="11330" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11177" class="Bound">n</a> <a id="11332" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11334" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11179" class="Bound">p</a><a id="11335" class="Symbol">)</a>
  <a id="11339" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="11343" class="Keyword">where</a>
  <a id="11351" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11351" class="Function">+-assoc-1</a> <a id="11361" class="Symbol">:</a> <a id="11363" class="Symbol">∀</a> <a id="11365" class="Symbol">(</a><a id="11366" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11366" class="Bound">n</a> <a id="11368" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11368" class="Bound">p</a> <a id="11370" class="Symbol">:</a> <a id="11372" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11373" class="Symbol">)</a> <a id="11375" class="Symbol">→</a> <a id="11377" class="Symbol">(</a><a id="11378" class="Number">1</a> <a id="11380" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11382" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11366" class="Bound">n</a><a id="11383" class="Symbol">)</a> <a id="11385" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11387" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11368" class="Bound">p</a> <a id="11389" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11391" class="Number">1</a> <a id="11393" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11395" class="Symbol">(</a><a id="11396" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11366" class="Bound">n</a> <a id="11398" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11400" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11368" class="Bound">p</a><a id="11401" class="Symbol">)</a>
  <a id="11405" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11351" class="Function">+-assoc-1</a> <a id="11415" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a> <a id="11417" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a> <a id="11419" class="Symbol">=</a>
    <a id="11425" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="11437" class="Symbol">(</a><a id="11438" class="Number">1</a> <a id="11440" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11442" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a><a id="11443" class="Symbol">)</a> <a id="11445" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11447" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a>
    <a id="11453" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11463" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11467" class="Symbol">(</a><a id="11468" class="Number">0</a> <a id="11470" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11472" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a><a id="11473" class="Symbol">)</a> <a id="11475" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11477" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a>
    <a id="11483" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11493" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11497" class="Symbol">((</a><a id="11499" class="Number">0</a> <a id="11501" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11503" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a><a id="11504" class="Symbol">)</a> <a id="11506" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11508" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a><a id="11509" class="Symbol">)</a>
    <a id="11515" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11518" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11523" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11527" class="Symbol">(</a><a id="11528" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11615" class="Function">+-assoc-0</a> <a id="11538" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a> <a id="11540" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a><a id="11541" class="Symbol">)</a> <a id="11543" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="11551" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11555" class="Symbol">(</a><a id="11556" class="Number">0</a> <a id="11558" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11560" class="Symbol">(</a><a id="11561" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a> <a id="11563" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11565" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a><a id="11566" class="Symbol">))</a>
    <a id="11573" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11583" class="Number">1</a> <a id="11585" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11587" class="Symbol">(</a><a id="11588" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11415" class="Bound">n</a> <a id="11590" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11592" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11417" class="Bound">p</a><a id="11593" class="Symbol">)</a>
    <a id="11599" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="11605" class="Keyword">where</a>
    <a id="11615" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11615" class="Function">+-assoc-0</a> <a id="11625" class="Symbol">:</a> <a id="11627" class="Symbol">∀</a> <a id="11629" class="Symbol">(</a><a id="11630" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11630" class="Bound">n</a> <a id="11632" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11632" class="Bound">p</a> <a id="11634" class="Symbol">:</a> <a id="11636" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11637" class="Symbol">)</a> <a id="11639" class="Symbol">→</a> <a id="11641" class="Symbol">(</a><a id="11642" class="Number">0</a> <a id="11644" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11646" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11630" class="Bound">n</a><a id="11647" class="Symbol">)</a> <a id="11649" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11651" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11632" class="Bound">p</a> <a id="11653" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11655" class="Number">0</a> <a id="11657" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11659" class="Symbol">(</a><a id="11660" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11630" class="Bound">n</a> <a id="11662" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11664" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11632" class="Bound">p</a><a id="11665" class="Symbol">)</a>
    <a id="11671" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11615" class="Function">+-assoc-0</a> <a id="11681" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11681" class="Bound">n</a> <a id="11683" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11683" class="Bound">p</a> <a id="11685" class="Symbol">=</a>
      <a id="11693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="11707" class="Symbol">(</a><a id="11708" class="Number">0</a> <a id="11710" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11712" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11681" class="Bound">n</a><a id="11713" class="Symbol">)</a> <a id="11715" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11717" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11683" class="Bound">p</a>
      <a id="11725" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11737" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11681" class="Bound">n</a> <a id="11739" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11741" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11683" class="Bound">p</a>
      <a id="11749" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11761" class="Number">0</a> <a id="11763" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11765" class="Symbol">(</a><a id="11766" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11681" class="Bound">n</a> <a id="11768" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11770" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11683" class="Bound">p</a><a id="11771" class="Symbol">)</a>
      <a id="11779" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}

## Terminology and notation

The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}/Quantifiers/).

Evidence for a universal quantifier is a function.  The notations

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

and

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="12999" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12999" class="Function">+-identityʳ</a> <a id="13011" class="Symbol">:</a> <a id="13013" class="Symbol">∀</a> <a id="13015" class="Symbol">(</a><a id="13016" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13016" class="Bound">m</a> <a id="13018" class="Symbol">:</a> <a id="13020" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13021" class="Symbol">)</a> <a id="13023" class="Symbol">→</a> <a id="13025" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13016" class="Bound">m</a> <a id="13027" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13029" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13034" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13036" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13016" class="Bound">m</a>
<a id="13038" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12999" class="Function">+-identityʳ</a> <a id="13050" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13055" class="Symbol">=</a>
  <a id="13059" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13069" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13074" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13076" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13083" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13091" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13098" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="13100" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12999" class="Function">+-identityʳ</a> <a id="13112" class="Symbol">(</a><a id="13113" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13117" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13117" class="Bound">m</a><a id="13118" class="Symbol">)</a> <a id="13120" class="Symbol">=</a>
  <a id="13124" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13134" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13138" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13117" class="Bound">m</a> <a id="13140" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13142" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13149" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13157" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13161" class="Symbol">(</a><a id="13162" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13117" class="Bound">m</a> <a id="13164" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13166" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="13170" class="Symbol">)</a>
  <a id="13174" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13177" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13182" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13186" class="Symbol">(</a><a id="13187" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12999" class="Function">+-identityʳ</a> <a id="13199" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13117" class="Bound">m</a><a id="13200" class="Symbol">)</a> <a id="13202" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="13208" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13212" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13117" class="Bound">m</a>
  <a id="13216" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="14656" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14656" class="Function">+-suc</a> <a id="14662" class="Symbol">:</a> <a id="14664" class="Symbol">∀</a> <a id="14666" class="Symbol">(</a><a id="14667" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14667" class="Bound">m</a> <a id="14669" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14669" class="Bound">n</a> <a id="14671" class="Symbol">:</a> <a id="14673" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14674" class="Symbol">)</a> <a id="14676" class="Symbol">→</a> <a id="14678" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14667" class="Bound">m</a> <a id="14680" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14682" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14686" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14669" class="Bound">n</a> <a id="14688" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14690" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14694" class="Symbol">(</a><a id="14695" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14667" class="Bound">m</a> <a id="14697" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14699" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14669" class="Bound">n</a><a id="14700" class="Symbol">)</a>
<a id="14702" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14656" class="Function">+-suc</a> <a id="14708" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14713" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14713" class="Bound">n</a> <a id="14715" class="Symbol">=</a>
  <a id="14719" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14729" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14734" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14736" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14740" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14713" class="Bound">n</a>
  <a id="14744" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14752" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14756" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14713" class="Bound">n</a>
  <a id="14760" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14768" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14772" class="Symbol">(</a><a id="14773" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14778" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14780" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14713" class="Bound">n</a><a id="14781" class="Symbol">)</a>
  <a id="14785" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="14787" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14656" class="Function">+-suc</a> <a id="14793" class="Symbol">(</a><a id="14794" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14798" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a><a id="14799" class="Symbol">)</a> <a id="14801" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a> <a id="14803" class="Symbol">=</a>
  <a id="14807" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14817" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14821" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a> <a id="14823" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14825" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14829" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a>
  <a id="14833" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14841" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14845" class="Symbol">(</a><a id="14846" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a> <a id="14848" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14850" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14854" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a><a id="14855" class="Symbol">)</a>
  <a id="14859" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="14862" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="14867" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14871" class="Symbol">(</a><a id="14872" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14656" class="Function">+-suc</a> <a id="14878" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a> <a id="14880" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a><a id="14881" class="Symbol">)</a> <a id="14883" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="14889" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14893" class="Symbol">(</a><a id="14894" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14898" class="Symbol">(</a><a id="14899" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a> <a id="14901" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14903" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a><a id="14904" class="Symbol">))</a>
  <a id="14909" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14917" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14921" class="Symbol">(</a><a id="14922" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14926" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14798" class="Bound">m</a> <a id="14928" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14930" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14801" class="Bound">n</a><a id="14931" class="Symbol">)</a>
  <a id="14935" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="16229" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16229" class="Function">+-comm</a> <a id="16236" class="Symbol">:</a> <a id="16238" class="Symbol">∀</a> <a id="16240" class="Symbol">(</a><a id="16241" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16241" class="Bound">m</a> <a id="16243" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16243" class="Bound">n</a> <a id="16245" class="Symbol">:</a> <a id="16247" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16248" class="Symbol">)</a> <a id="16250" class="Symbol">→</a> <a id="16252" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16241" class="Bound">m</a> <a id="16254" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16256" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16243" class="Bound">n</a> <a id="16258" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16260" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16243" class="Bound">n</a> <a id="16262" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16264" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16241" class="Bound">m</a>
<a id="16266" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16229" class="Function">+-comm</a> <a id="16273" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16273" class="Bound">m</a> <a id="16275" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16280" class="Symbol">=</a>
  <a id="16284" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16294" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16273" class="Bound">m</a> <a id="16296" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16298" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="16305" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16308" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12999" class="Function">+-identityʳ</a> <a id="16320" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16273" class="Bound">m</a> <a id="16322" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16328" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16273" class="Bound">m</a>
  <a id="16332" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16340" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16345" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16347" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16273" class="Bound">m</a>
  <a id="16351" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="16353" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16229" class="Function">+-comm</a> <a id="16360" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a> <a id="16362" class="Symbol">(</a><a id="16363" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16367" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a><a id="16368" class="Symbol">)</a> <a id="16370" class="Symbol">=</a>
  <a id="16374" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16384" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a> <a id="16386" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16388" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16392" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a>
  <a id="16396" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16399" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14656" class="Function">+-suc</a> <a id="16405" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a> <a id="16407" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a> <a id="16409" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16415" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16419" class="Symbol">(</a><a id="16420" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a> <a id="16422" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16424" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a><a id="16425" class="Symbol">)</a>
  <a id="16429" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16432" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16437" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16441" class="Symbol">(</a><a id="16442" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16229" class="Function">+-comm</a> <a id="16449" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a> <a id="16451" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a><a id="16452" class="Symbol">)</a> <a id="16454" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16460" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16464" class="Symbol">(</a><a id="16465" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a> <a id="16467" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16469" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a><a id="16470" class="Symbol">)</a>
  <a id="16474" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16482" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16486" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16367" class="Bound">n</a> <a id="16488" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16490" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16360" class="Bound">m</a>
  <a id="16494" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example:
{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="18040" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18040" class="Function">+-rearrange</a> <a id="18052" class="Symbol">:</a> <a id="18054" class="Symbol">∀</a> <a id="18056" class="Symbol">(</a><a id="18057" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18057" class="Bound">m</a> <a id="18059" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18059" class="Bound">n</a> <a id="18061" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18061" class="Bound">p</a> <a id="18063" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18063" class="Bound">q</a> <a id="18065" class="Symbol">:</a> <a id="18067" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18068" class="Symbol">)</a> <a id="18070" class="Symbol">→</a> <a id="18072" class="Symbol">(</a><a id="18073" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18057" class="Bound">m</a> <a id="18075" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18077" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18059" class="Bound">n</a><a id="18078" class="Symbol">)</a> <a id="18080" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18082" class="Symbol">(</a><a id="18083" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18061" class="Bound">p</a> <a id="18085" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18087" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18063" class="Bound">q</a><a id="18088" class="Symbol">)</a> <a id="18090" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18092" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18057" class="Bound">m</a> <a id="18094" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18096" class="Symbol">(</a><a id="18097" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18059" class="Bound">n</a> <a id="18099" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18101" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18061" class="Bound">p</a><a id="18102" class="Symbol">)</a> <a id="18104" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18106" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18063" class="Bound">q</a>
<a id="18108" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18040" class="Function">+-rearrange</a> <a id="18120" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18122" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18124" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a> <a id="18126" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a> <a id="18128" class="Symbol">=</a>
  <a id="18132" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18142" class="Symbol">(</a><a id="18143" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18145" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18147" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a><a id="18148" class="Symbol">)</a> <a id="18150" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18152" class="Symbol">(</a><a id="18153" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a> <a id="18155" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18157" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18158" class="Symbol">)</a>
  <a id="18162" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18165" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="18173" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18175" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18177" class="Symbol">(</a><a id="18178" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a> <a id="18180" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18182" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18183" class="Symbol">)</a> <a id="18185" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18191" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18193" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18195" class="Symbol">(</a><a id="18196" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18198" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18200" class="Symbol">(</a><a id="18201" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a> <a id="18203" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18205" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18206" class="Symbol">))</a>
  <a id="18211" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18214" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18219" class="Symbol">(</a><a id="18220" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18222" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="18224" class="Symbol">)</a> <a id="18226" class="Symbol">(</a><a id="18227" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18231" class="Symbol">(</a><a id="18232" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="18240" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18242" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a> <a id="18244" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18245" class="Symbol">))</a> <a id="18248" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18254" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18256" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18258" class="Symbol">((</a><a id="18260" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18262" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18264" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a><a id="18265" class="Symbol">)</a> <a id="18267" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18269" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18270" class="Symbol">)</a>
  <a id="18274" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18277" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18281" class="Symbol">(</a><a id="18282" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7762" class="Function">+-assoc</a> <a id="18290" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18292" class="Symbol">(</a><a id="18293" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18295" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18297" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a><a id="18298" class="Symbol">)</a> <a id="18300" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a><a id="18301" class="Symbol">)</a> <a id="18303" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18309" class="Symbol">(</a><a id="18310" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18120" class="Bound">m</a> <a id="18312" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18314" class="Symbol">(</a><a id="18315" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18122" class="Bound">n</a> <a id="18317" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18319" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18124" class="Bound">p</a><a id="18320" class="Symbol">))</a> <a id="18323" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18325" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18126" class="Bound">q</a>
  <a id="18329" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc n p q)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:

     -- In the beginning, we know nothing about associativity.

Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:

    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:

    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again:

    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now:

    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).

{% raw %}<pre class="Agda"><a id="21747" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="21963" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21963" class="Function">+-assoc′</a> <a id="21972" class="Symbol">:</a> <a id="21974" class="Symbol">∀</a> <a id="21976" class="Symbol">(</a><a id="21977" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21977" class="Bound">m</a> <a id="21979" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21979" class="Bound">n</a> <a id="21981" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21981" class="Bound">p</a> <a id="21983" class="Symbol">:</a> <a id="21985" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21986" class="Symbol">)</a> <a id="21988" class="Symbol">→</a> <a id="21990" class="Symbol">(</a><a id="21991" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21977" class="Bound">m</a> <a id="21993" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21995" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21979" class="Bound">n</a><a id="21996" class="Symbol">)</a> <a id="21998" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22000" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21981" class="Bound">p</a> <a id="22002" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="22004" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21977" class="Bound">m</a> <a id="22006" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22008" class="Symbol">(</a><a id="22009" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21979" class="Bound">n</a> <a id="22011" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22013" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21981" class="Bound">p</a><a id="22014" class="Symbol">)</a>
<a id="22016" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21963" class="Function">+-assoc′</a> <a id="22025" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="22033" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22033" class="Bound">n</a> <a id="22035" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22035" class="Bound">p</a>                          <a id="22062" class="Symbol">=</a>  <a id="22065" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="22070" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21963" class="Function">+-assoc′</a> <a id="22079" class="Symbol">(</a><a id="22080" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22084" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22084" class="Bound">m</a><a id="22085" class="Symbol">)</a> <a id="22087" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22087" class="Bound">n</a> <a id="22089" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22089" class="Bound">p</a>  <a id="22092" class="Keyword">rewrite</a> <a id="22100" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21963" class="Function">+-assoc′</a> <a id="22109" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22084" class="Bound">m</a> <a id="22111" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22087" class="Bound">n</a> <a id="22113" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22089" class="Bound">p</a>  <a id="22116" class="Symbol">=</a>  <a id="22119" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="23022" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23022" class="Function">+-identity′</a> <a id="23034" class="Symbol">:</a> <a id="23036" class="Symbol">∀</a> <a id="23038" class="Symbol">(</a><a id="23039" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23039" class="Bound">n</a> <a id="23041" class="Symbol">:</a> <a id="23043" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23044" class="Symbol">)</a> <a id="23046" class="Symbol">→</a> <a id="23048" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23039" class="Bound">n</a> <a id="23050" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23052" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23057" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23059" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23039" class="Bound">n</a>
<a id="23061" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23022" class="Function">+-identity′</a> <a id="23073" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23078" class="Symbol">=</a> <a id="23080" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23085" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23022" class="Function">+-identity′</a> <a id="23097" class="Symbol">(</a><a id="23098" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23102" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23102" class="Bound">n</a><a id="23103" class="Symbol">)</a> <a id="23105" class="Keyword">rewrite</a> <a id="23113" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23022" class="Function">+-identity′</a> <a id="23125" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23102" class="Bound">n</a> <a id="23127" class="Symbol">=</a> <a id="23129" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="23135" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23135" class="Function">+-suc′</a> <a id="23142" class="Symbol">:</a> <a id="23144" class="Symbol">∀</a> <a id="23146" class="Symbol">(</a><a id="23147" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23147" class="Bound">m</a> <a id="23149" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23149" class="Bound">n</a> <a id="23151" class="Symbol">:</a> <a id="23153" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23154" class="Symbol">)</a> <a id="23156" class="Symbol">→</a> <a id="23158" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23147" class="Bound">m</a> <a id="23160" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23162" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23166" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23149" class="Bound">n</a> <a id="23168" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23170" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23174" class="Symbol">(</a><a id="23175" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23147" class="Bound">m</a> <a id="23177" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23179" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23149" class="Bound">n</a><a id="23180" class="Symbol">)</a>
<a id="23182" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23135" class="Function">+-suc′</a> <a id="23189" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23194" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23194" class="Bound">n</a> <a id="23196" class="Symbol">=</a> <a id="23198" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23203" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23135" class="Function">+-suc′</a> <a id="23210" class="Symbol">(</a><a id="23211" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23215" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23215" class="Bound">m</a><a id="23216" class="Symbol">)</a> <a id="23218" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23218" class="Bound">n</a> <a id="23220" class="Keyword">rewrite</a> <a id="23228" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23135" class="Function">+-suc′</a> <a id="23235" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23215" class="Bound">m</a> <a id="23237" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23218" class="Bound">n</a> <a id="23239" class="Symbol">=</a> <a id="23241" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="23247" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Function">+-comm′</a> <a id="23255" class="Symbol">:</a> <a id="23257" class="Symbol">∀</a> <a id="23259" class="Symbol">(</a><a id="23260" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23260" class="Bound">m</a> <a id="23262" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23262" class="Bound">n</a> <a id="23264" class="Symbol">:</a> <a id="23266" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23267" class="Symbol">)</a> <a id="23269" class="Symbol">→</a> <a id="23271" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23260" class="Bound">m</a> <a id="23273" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23275" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23262" class="Bound">n</a> <a id="23277" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23279" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23262" class="Bound">n</a> <a id="23281" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23283" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23260" class="Bound">m</a>
<a id="23285" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Function">+-comm′</a> <a id="23293" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23295" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23300" class="Keyword">rewrite</a> <a id="23308" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23022" class="Function">+-identity′</a> <a id="23320" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23293" class="Bound">m</a> <a id="23322" class="Symbol">=</a> <a id="23324" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23329" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Function">+-comm′</a> <a id="23337" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23337" class="Bound">m</a> <a id="23339" class="Symbol">(</a><a id="23340" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23344" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23344" class="Bound">n</a><a id="23345" class="Symbol">)</a> <a id="23347" class="Keyword">rewrite</a> <a id="23355" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23135" class="Function">+-suc′</a> <a id="23362" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23337" class="Bound">m</a> <a id="23364" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23344" class="Bound">n</a> <a id="23366" class="Symbol">|</a> <a id="23368" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23247" class="Function">+-comm′</a> <a id="23376" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23337" class="Bound">m</a> <a id="23378" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23344" class="Bound">n</a> <a id="23380" class="Symbol">=</a> <a id="23382" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgment.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

{% raw %}<pre class="Agda"><a id="26922" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27147" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27348" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

{% raw %}<pre class="Agda"><a id="27616" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

{% raw %}<pre class="Agda"><a id="27781" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27990" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `+*^` (stretch)

Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="28773" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="28910" class="Keyword">import</a> <a id="28917" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="28937" class="Keyword">using</a> <a id="28943" class="Symbol">(</a><a id="28944" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="28951" class="Symbol">;</a> <a id="28953" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="28964" class="Symbol">;</a> <a id="28966" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="28971" class="Symbol">;</a> <a id="28973" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="28979" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
