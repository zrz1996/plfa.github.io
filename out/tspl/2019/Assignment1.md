---
src       : "courses/tspl/2019/Assignment1.lagda.md"
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /TSPL/2019/Assignment1/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}" class="Module">Assignment1</a> <a id="131" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).



## Imports

{% raw %}<pre class="Agda"><a id="1199" class="Keyword">import</a> <a id="1206" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1244" class="Symbol">as</a> <a id="1247" class="Module">Eq</a>
<a id="1250" class="Keyword">open</a> <a id="1255" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1258" class="Keyword">using</a> <a id="1264" class="Symbol">(</a><a id="1265" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1268" class="Symbol">;</a> <a id="1270" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1274" class="Symbol">;</a> <a id="1276" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1280" class="Symbol">;</a> <a id="1282" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1285" class="Symbol">)</a>
<a id="1287" class="Keyword">open</a> <a id="1292" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1307" class="Keyword">using</a> <a id="1313" class="Symbol">(</a><a id="1314" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1320" class="Symbol">;</a> <a id="1322" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1327" class="Symbol">;</a> <a id="1329" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1335" class="Symbol">;</a> <a id="1337" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1339" class="Symbol">)</a>
<a id="1341" class="Keyword">open</a> <a id="1346" class="Keyword">import</a> <a id="1353" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1362" class="Keyword">using</a> <a id="1368" class="Symbol">(</a><a id="1369" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1370" class="Symbol">;</a> <a id="1372" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1376" class="Symbol">;</a> <a id="1378" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1381" class="Symbol">;</a> <a id="1383" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1386" class="Symbol">;</a> <a id="1388" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1391" class="Symbol">;</a> <a id="1393" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1396" class="Symbol">;</a> <a id="1398" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="1401" class="Symbol">;</a> <a id="1403" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="1406" class="Symbol">;</a> <a id="1408" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="1411" class="Symbol">)</a>
<a id="1413" class="Keyword">open</a> <a id="1418" class="Keyword">import</a> <a id="1425" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="1445" class="Keyword">using</a> <a id="1451" class="Symbol">(</a><a id="1452" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="1459" class="Symbol">;</a> <a id="1461" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="1472" class="Symbol">;</a> <a id="1474" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="1479" class="Symbol">;</a> <a id="1481" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="1487" class="Symbol">;</a>
  <a id="1491" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="1497" class="Symbol">;</a> <a id="1499" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="1506" class="Symbol">;</a> <a id="1508" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1517" class="Symbol">;</a> <a id="1519" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1526" class="Symbol">;</a> <a id="1528" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1537" class="Symbol">;</a> <a id="1539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1548" class="Symbol">;</a> <a id="1550" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1558" class="Symbol">)</a>
<a id="1560" class="Keyword">open</a> <a id="1565" class="Keyword">import</a> <a id="1572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="1593" class="Keyword">using</a> <a id="1599" class="Symbol">(</a><a id="1600" href="plfa.part1.Relations.html#18383" class="Datatype Operator">_&lt;_</a><a id="1603" class="Symbol">;</a> <a id="1605" href="plfa.part1.Relations.html#18410" class="InductiveConstructor">z&lt;s</a><a id="1608" class="Symbol">;</a> <a id="1610" href="plfa.part1.Relations.html#18467" class="InductiveConstructor">s&lt;s</a><a id="1613" class="Symbol">;</a> <a id="1615" href="plfa.part1.Relations.html#21136" class="InductiveConstructor">zero</a><a id="1619" class="Symbol">;</a> <a id="1621" href="plfa.part1.Relations.html#21178" class="InductiveConstructor">suc</a><a id="1624" class="Symbol">;</a> <a id="1626" href="plfa.part1.Relations.html#21081" class="Datatype">even</a><a id="1630" class="Symbol">;</a> <a id="1632" href="plfa.part1.Relations.html#21101" class="Datatype">odd</a><a id="1635" class="Symbol">)</a>
</pre>{% endraw %}
## Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
{% raw %}<pre class="Agda"><a id="2491" class="Keyword">data</a> <a id="Bin"></a><a id="2496" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2496" class="Datatype">Bin</a> <a id="2500" class="Symbol">:</a> <a id="2502" class="PrimitiveType">Set</a> <a id="2506" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="2514" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2514" class="InductiveConstructor">nil</a> <a id="2518" class="Symbol">:</a> <a id="2520" href="Assignment1.html#2496" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="2526" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2526" class="InductiveConstructor Operator">x0_</a> <a id="2530" class="Symbol">:</a> <a id="2532" href="Assignment1.html#2496" class="Datatype">Bin</a> <a id="2536" class="Symbol">→</a> <a id="2538" href="Assignment1.html#2496" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="2544" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment1.md %}{% raw %}#2544" class="InductiveConstructor Operator">x1_</a> <a id="2548" class="Symbol">:</a> <a id="2550" href="Assignment1.html#2496" class="Datatype">Bin</a> <a id="2554" class="Symbol">→</a> <a id="2556" href="Assignment1.html#2496" class="Datatype">Bin</a>
</pre>{% endraw %}For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

## Induction

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
