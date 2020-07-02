---
src       : "src/plfa/part1/Relations.lagda.md"
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

{% raw %}<pre class="Agda"><a id="161" class="Keyword">module</a> <a id="168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

{% raw %}<pre class="Agda"><a id="354" class="Keyword">import</a> <a id="361" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="399" class="Symbol">as</a> <a id="402" class="Module">Eq</a>
<a id="405" class="Keyword">open</a> <a id="410" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="413" class="Keyword">using</a> <a id="419" class="Symbol">(</a><a id="420" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="423" class="Symbol">;</a> <a id="425" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="429" class="Symbol">;</a> <a id="431" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="435" class="Symbol">)</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="458" class="Keyword">using</a> <a id="464" class="Symbol">(</a><a id="465" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="466" class="Symbol">;</a> <a id="468" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="472" class="Symbol">;</a> <a id="474" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="477" class="Symbol">;</a> <a id="479" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="482" class="Symbol">)</a>
<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="516" class="Keyword">using</a> <a id="522" class="Symbol">(</a><a id="523" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="529" class="Symbol">)</a>
</pre>{% endraw %}

## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
{% raw %}<pre class="Agda"><a id="1190" class="Keyword">data</a> <a id="_≤_"></a><a id="1195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1195" class="Datatype Operator">_≤_</a> <a id="1199" class="Symbol">:</a> <a id="1201" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1203" class="Symbol">→</a> <a id="1205" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1207" class="Symbol">→</a> <a id="1209" class="PrimitiveType">Set</a> <a id="1213" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1222" class="InductiveConstructor">z≤n</a> <a id="1226" class="Symbol">:</a> <a id="1228" class="Symbol">∀</a> <a id="1230" class="Symbol">{</a><a id="1231" href="plfa.part1.Relations.html#1231" class="Bound">n</a> <a id="1233" class="Symbol">:</a> <a id="1235" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1236" class="Symbol">}</a>
      <a id="1244" class="Comment">--------</a>
    <a id="1257" class="Symbol">→</a> <a id="1259" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1195" class="Datatype Operator">≤</a> <a id="1266" href="plfa.part1.Relations.html#1231" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1271" class="InductiveConstructor">s≤s</a> <a id="1275" class="Symbol">:</a> <a id="1277" class="Symbol">∀</a> <a id="1279" class="Symbol">{</a><a id="1280" href="plfa.part1.Relations.html#1280" class="Bound">m</a> <a id="1282" href="plfa.part1.Relations.html#1282" class="Bound">n</a> <a id="1284" class="Symbol">:</a> <a id="1286" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1287" class="Symbol">}</a>
    <a id="1293" class="Symbol">→</a> <a id="1295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1280" class="Bound">m</a> <a id="1297" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="1299" href="plfa.part1.Relations.html#1282" class="Bound">n</a>
      <a id="1307" class="Comment">-------------</a>
    <a id="1325" class="Symbol">→</a> <a id="1327" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1280" class="Bound">m</a> <a id="1333" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="1335" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1339" href="plfa.part1.Relations.html#1282" class="Bound">n</a>
</pre>{% endraw %}Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
{% raw %}<pre class="Agda"><a id="2601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#2601" class="Function">_</a> <a id="2603" class="Symbol">:</a> <a id="2605" class="Number">2</a> <a id="2607" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="2609" class="Number">4</a>
<a id="2611" class="Symbol">_</a> <a id="2613" class="Symbol">=</a> <a id="2615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1271" class="InductiveConstructor">s≤s</a> <a id="2619" class="Symbol">(</a><a id="2620" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="2624" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a><a id="2627" class="Symbol">)</a>
</pre>{% endraw %}



## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{% raw %}<pre class="Agda"><a id="3606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3606" class="Function">_</a> <a id="3608" class="Symbol">:</a> <a id="3610" class="Number">2</a> <a id="3612" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="3614" class="Number">4</a>
<a id="3616" class="Symbol">_</a> <a id="3618" class="Symbol">=</a> <a id="3620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1271" class="InductiveConstructor">s≤s</a> <a id="3624" class="Symbol">{</a><a id="3625" class="Number">1</a><a id="3626" class="Symbol">}</a> <a id="3628" class="Symbol">{</a><a id="3629" class="Number">3</a><a id="3630" class="Symbol">}</a> <a id="3632" class="Symbol">(</a><a id="3633" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="3637" class="Symbol">{</a><a id="3638" class="Number">0</a><a id="3639" class="Symbol">}</a> <a id="3641" class="Symbol">{</a><a id="3642" class="Number">2</a><a id="3643" class="Symbol">}</a> <a id="3645" class="Symbol">(</a><a id="3646" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a> <a id="3650" class="Symbol">{</a><a id="3651" class="Number">2</a><a id="3652" class="Symbol">}))</a>
</pre>{% endraw %}One may also identify implicit arguments by name:
{% raw %}<pre class="Agda"><a id="3714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3714" class="Function">_</a> <a id="3716" class="Symbol">:</a> <a id="3718" class="Number">2</a> <a id="3720" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="3722" class="Number">4</a>
<a id="3724" class="Symbol">_</a> <a id="3726" class="Symbol">=</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1271" class="InductiveConstructor">s≤s</a> <a id="3732" class="Symbol">{</a><a id="3733" class="Argument">m</a> <a id="3735" class="Symbol">=</a> <a id="3737" class="Number">1</a><a id="3738" class="Symbol">}</a> <a id="3740" class="Symbol">{</a><a id="3741" class="Argument">n</a> <a id="3743" class="Symbol">=</a> <a id="3745" class="Number">3</a><a id="3746" class="Symbol">}</a> <a id="3748" class="Symbol">(</a><a id="3749" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="3753" class="Symbol">{</a><a id="3754" class="Argument">m</a> <a id="3756" class="Symbol">=</a> <a id="3758" class="Number">0</a><a id="3759" class="Symbol">}</a> <a id="3761" class="Symbol">{</a><a id="3762" class="Argument">n</a> <a id="3764" class="Symbol">=</a> <a id="3766" class="Number">2</a><a id="3767" class="Symbol">}</a> <a id="3769" class="Symbol">(</a><a id="3770" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a> <a id="3774" class="Symbol">{</a><a id="3775" class="Argument">n</a> <a id="3777" class="Symbol">=</a> <a id="3779" class="Number">2</a><a id="3780" class="Symbol">}))</a>
</pre>{% endraw %}In the latter format, you may only supply some implicit arguments:
{% raw %}<pre class="Agda"><a id="3859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3859" class="Function">_</a> <a id="3861" class="Symbol">:</a> <a id="3863" class="Number">2</a> <a id="3865" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="3867" class="Number">4</a>
<a id="3869" class="Symbol">_</a> <a id="3871" class="Symbol">=</a> <a id="3873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1271" class="InductiveConstructor">s≤s</a> <a id="3877" class="Symbol">{</a><a id="3878" class="Argument">n</a> <a id="3880" class="Symbol">=</a> <a id="3882" class="Number">3</a><a id="3883" class="Symbol">}</a> <a id="3885" class="Symbol">(</a><a id="3886" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="3890" class="Symbol">{</a><a id="3891" class="Argument">n</a> <a id="3893" class="Symbol">=</a> <a id="3895" class="Number">2</a><a id="3896" class="Symbol">}</a> <a id="3898" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a><a id="3901" class="Symbol">)</a>
</pre>{% endraw %}It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
{% raw %}<pre class="Agda"><a id="4046" class="Keyword">infix</a> <a id="4052" class="Number">4</a> <a id="4054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1195" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}/Decidable/).


## Inversion

In our definitions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5072" class="Function">inv-s≤s</a> <a id="5080" class="Symbol">:</a> <a id="5082" class="Symbol">∀</a> <a id="5084" class="Symbol">{</a><a id="5085" href="plfa.part1.Relations.html#5085" class="Bound">m</a> <a id="5087" href="plfa.part1.Relations.html#5087" class="Bound">n</a> <a id="5089" class="Symbol">:</a> <a id="5091" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5092" class="Symbol">}</a>
  <a id="5096" class="Symbol">→</a> <a id="5098" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5085" class="Bound">m</a> <a id="5104" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5106" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5110" href="plfa.part1.Relations.html#5087" class="Bound">n</a>
    <a id="5116" class="Comment">-------------</a>
  <a id="5132" class="Symbol">→</a> <a id="5134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5085" class="Bound">m</a> <a id="5136" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5138" href="plfa.part1.Relations.html#5087" class="Bound">n</a>
<a id="5140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5072" class="Function">inv-s≤s</a> <a id="5148" class="Symbol">(</a><a id="5149" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="5153" href="plfa.part1.Relations.html#5153" class="Bound">m≤n</a><a id="5156" class="Symbol">)</a> <a id="5158" class="Symbol">=</a> <a id="5160" href="plfa.part1.Relations.html#5153" class="Bound">m≤n</a>
</pre>{% endraw %}Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="5668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5668" class="Function">inv-z≤n</a> <a id="5676" class="Symbol">:</a> <a id="5678" class="Symbol">∀</a> <a id="5680" class="Symbol">{</a><a id="5681" href="plfa.part1.Relations.html#5681" class="Bound">m</a> <a id="5683" class="Symbol">:</a> <a id="5685" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5686" class="Symbol">}</a>
  <a id="5690" class="Symbol">→</a> <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5681" class="Bound">m</a> <a id="5694" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5696" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="5705" class="Comment">--------</a>
  <a id="5716" class="Symbol">→</a> <a id="5718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5681" class="Bound">m</a> <a id="5720" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5722" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="5727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5668" class="Function">inv-z≤n</a> <a id="5735" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a> <a id="5739" class="Symbol">=</a> <a id="5741" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

{% raw %}<pre class="Agda"><a id="7243" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7338" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="7638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7638" class="Function">≤-refl</a> <a id="7645" class="Symbol">:</a> <a id="7647" class="Symbol">∀</a> <a id="7649" class="Symbol">{</a><a id="7650" href="plfa.part1.Relations.html#7650" class="Bound">n</a> <a id="7652" class="Symbol">:</a> <a id="7654" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7655" class="Symbol">}</a>
    <a id="7661" class="Comment">-----</a>
  <a id="7669" class="Symbol">→</a> <a id="7671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7650" class="Bound">n</a> <a id="7673" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="7675" href="plfa.part1.Relations.html#7650" class="Bound">n</a>
<a id="7677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7638" class="Function">≤-refl</a> <a id="7684" class="Symbol">{</a><a id="7685" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="7689" class="Symbol">}</a> <a id="7691" class="Symbol">=</a> <a id="7693" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="7697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7638" class="Function">≤-refl</a> <a id="7704" class="Symbol">{</a><a id="7705" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7709" href="plfa.part1.Relations.html#7709" class="Bound">n</a><a id="7710" class="Symbol">}</a> <a id="7712" class="Symbol">=</a> <a id="7714" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="7718" href="plfa.part1.Relations.html#7638" class="Function">≤-refl</a>
</pre>{% endraw %}The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8355" class="Function">≤-trans</a> <a id="8363" class="Symbol">:</a> <a id="8365" class="Symbol">∀</a> <a id="8367" class="Symbol">{</a><a id="8368" href="plfa.part1.Relations.html#8368" class="Bound">m</a> <a id="8370" href="plfa.part1.Relations.html#8370" class="Bound">n</a> <a id="8372" href="plfa.part1.Relations.html#8372" class="Bound">p</a> <a id="8374" class="Symbol">:</a> <a id="8376" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8377" class="Symbol">}</a>
  <a id="8381" class="Symbol">→</a> <a id="8383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8368" class="Bound">m</a> <a id="8385" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8387" href="plfa.part1.Relations.html#8370" class="Bound">n</a>
  <a id="8391" class="Symbol">→</a> <a id="8393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8370" class="Bound">n</a> <a id="8395" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8397" href="plfa.part1.Relations.html#8372" class="Bound">p</a>
    <a id="8403" class="Comment">-----</a>
  <a id="8411" class="Symbol">→</a> <a id="8413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8368" class="Bound">m</a> <a id="8415" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8417" href="plfa.part1.Relations.html#8372" class="Bound">p</a>
<a id="8419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8355" class="Function">≤-trans</a> <a id="8427" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="8437" class="Symbol">_</a>          <a id="8448" class="Symbol">=</a>  <a id="8451" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="8455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8355" class="Function">≤-trans</a> <a id="8463" class="Symbol">(</a><a id="8464" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8468" href="plfa.part1.Relations.html#8468" class="Bound">m≤n</a><a id="8471" class="Symbol">)</a> <a id="8473" class="Symbol">(</a><a id="8474" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8478" href="plfa.part1.Relations.html#8478" class="Bound">n≤p</a><a id="8481" class="Symbol">)</a>  <a id="8484" class="Symbol">=</a>  <a id="8487" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8491" class="Symbol">(</a><a id="8492" href="plfa.part1.Relations.html#8355" class="Function">≤-trans</a> <a id="8500" href="plfa.part1.Relations.html#8468" class="Bound">m≤n</a> <a id="8504" href="plfa.part1.Relations.html#8478" class="Bound">n≤p</a><a id="8507" class="Symbol">)</a>
</pre>{% endraw %}Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9468" class="Function">≤-trans′</a> <a id="9477" class="Symbol">:</a> <a id="9479" class="Symbol">∀</a> <a id="9481" class="Symbol">(</a><a id="9482" href="plfa.part1.Relations.html#9482" class="Bound">m</a> <a id="9484" href="plfa.part1.Relations.html#9484" class="Bound">n</a> <a id="9486" href="plfa.part1.Relations.html#9486" class="Bound">p</a> <a id="9488" class="Symbol">:</a> <a id="9490" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9491" class="Symbol">)</a>
  <a id="9495" class="Symbol">→</a> <a id="9497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9482" class="Bound">m</a> <a id="9499" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9501" href="plfa.part1.Relations.html#9484" class="Bound">n</a>
  <a id="9505" class="Symbol">→</a> <a id="9507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9484" class="Bound">n</a> <a id="9509" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9511" href="plfa.part1.Relations.html#9486" class="Bound">p</a>
    <a id="9517" class="Comment">-----</a>
  <a id="9525" class="Symbol">→</a> <a id="9527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9482" class="Bound">m</a> <a id="9529" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9531" href="plfa.part1.Relations.html#9486" class="Bound">p</a>
<a id="9533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9468" class="Function">≤-trans′</a> <a id="9542" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="9550" class="Symbol">_</a>       <a id="9558" class="Symbol">_</a>       <a id="9566" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="9576" class="Symbol">_</a>          <a id="9587" class="Symbol">=</a>  <a id="9590" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="9594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9468" class="Function">≤-trans′</a> <a id="9603" class="Symbol">(</a><a id="9604" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9608" href="plfa.part1.Relations.html#9608" class="Bound">m</a><a id="9609" class="Symbol">)</a> <a id="9611" class="Symbol">(</a><a id="9612" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9616" href="plfa.part1.Relations.html#9616" class="Bound">n</a><a id="9617" class="Symbol">)</a> <a id="9619" class="Symbol">(</a><a id="9620" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9624" href="plfa.part1.Relations.html#9624" class="Bound">p</a><a id="9625" class="Symbol">)</a> <a id="9627" class="Symbol">(</a><a id="9628" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9632" href="plfa.part1.Relations.html#9632" class="Bound">m≤n</a><a id="9635" class="Symbol">)</a> <a id="9637" class="Symbol">(</a><a id="9638" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9642" href="plfa.part1.Relations.html#9642" class="Bound">n≤p</a><a id="9645" class="Symbol">)</a>  <a id="9648" class="Symbol">=</a>  <a id="9651" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9655" class="Symbol">(</a><a id="9656" href="plfa.part1.Relations.html#9468" class="Function">≤-trans′</a> <a id="9665" href="plfa.part1.Relations.html#9608" class="Bound">m</a> <a id="9667" href="plfa.part1.Relations.html#9616" class="Bound">n</a> <a id="9669" href="plfa.part1.Relations.html#9624" class="Bound">p</a> <a id="9671" href="plfa.part1.Relations.html#9632" class="Bound">m≤n</a> <a id="9675" href="plfa.part1.Relations.html#9642" class="Bound">n≤p</a><a id="9678" class="Symbol">)</a>
</pre>{% endraw %}One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10423" class="Function">≤-antisym</a> <a id="10433" class="Symbol">:</a> <a id="10435" class="Symbol">∀</a> <a id="10437" class="Symbol">{</a><a id="10438" href="plfa.part1.Relations.html#10438" class="Bound">m</a> <a id="10440" href="plfa.part1.Relations.html#10440" class="Bound">n</a> <a id="10442" class="Symbol">:</a> <a id="10444" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10445" class="Symbol">}</a>
  <a id="10449" class="Symbol">→</a> <a id="10451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10438" class="Bound">m</a> <a id="10453" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="10455" href="plfa.part1.Relations.html#10440" class="Bound">n</a>
  <a id="10459" class="Symbol">→</a> <a id="10461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10440" class="Bound">n</a> <a id="10463" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="10465" href="plfa.part1.Relations.html#10438" class="Bound">m</a>
    <a id="10471" class="Comment">-----</a>
  <a id="10479" class="Symbol">→</a> <a id="10481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10438" class="Bound">m</a> <a id="10483" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10485" href="plfa.part1.Relations.html#10440" class="Bound">n</a>
<a id="10487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10423" class="Function">≤-antisym</a> <a id="10497" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="10507" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>        <a id="10518" class="Symbol">=</a>  <a id="10521" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="10526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10423" class="Function">≤-antisym</a> <a id="10536" class="Symbol">(</a><a id="10537" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="10541" href="plfa.part1.Relations.html#10541" class="Bound">m≤n</a><a id="10544" class="Symbol">)</a> <a id="10546" class="Symbol">(</a><a id="10547" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="10551" href="plfa.part1.Relations.html#10551" class="Bound">n≤m</a><a id="10554" class="Symbol">)</a>  <a id="10557" class="Symbol">=</a>  <a id="10560" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10565" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10569" class="Symbol">(</a><a id="10570" href="plfa.part1.Relations.html#10423" class="Function">≤-antisym</a> <a id="10580" href="plfa.part1.Relations.html#10541" class="Bound">m≤n</a> <a id="10584" href="plfa.part1.Relations.html#10551" class="Bound">n≤m</a><a id="10587" class="Symbol">)</a>
</pre>{% endraw %}Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

{% raw %}<pre class="Agda"><a id="11393" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="11647" class="Keyword">data</a> <a id="Total"></a><a id="11652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11652" class="Datatype">Total</a> <a id="11658" class="Symbol">(</a><a id="11659" href="plfa.part1.Relations.html#11659" class="Bound">m</a> <a id="11661" href="plfa.part1.Relations.html#11661" class="Bound">n</a> <a id="11663" class="Symbol">:</a> <a id="11665" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11666" class="Symbol">)</a> <a id="11668" class="Symbol">:</a> <a id="11670" class="PrimitiveType">Set</a> <a id="11674" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11683" class="InductiveConstructor">forward</a> <a id="11691" class="Symbol">:</a>
      <a id="11699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11659" class="Bound">m</a> <a id="11701" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="11703" href="plfa.part1.Relations.html#11661" class="Bound">n</a>
      <a id="11711" class="Comment">---------</a>
    <a id="11725" class="Symbol">→</a> <a id="11727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11652" class="Datatype">Total</a> <a id="11733" href="plfa.part1.Relations.html#11659" class="Bound">m</a> <a id="11735" href="plfa.part1.Relations.html#11661" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11740" class="InductiveConstructor">flipped</a> <a id="11748" class="Symbol">:</a>
      <a id="11756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11661" class="Bound">n</a> <a id="11758" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="11760" href="plfa.part1.Relations.html#11659" class="Bound">m</a>
      <a id="11768" class="Comment">---------</a>
    <a id="11782" class="Symbol">→</a> <a id="11784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11652" class="Datatype">Total</a> <a id="11790" href="plfa.part1.Relations.html#11659" class="Bound">m</a> <a id="11792" href="plfa.part1.Relations.html#11661" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12281" class="Keyword">data</a> <a id="Total′"></a><a id="12286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12286" class="Datatype">Total′</a> <a id="12293" class="Symbol">:</a> <a id="12295" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12297" class="Symbol">→</a> <a id="12299" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12301" class="Symbol">→</a> <a id="12303" class="PrimitiveType">Set</a> <a id="12307" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12316" class="InductiveConstructor">forward′</a> <a id="12325" class="Symbol">:</a> <a id="12327" class="Symbol">∀</a> <a id="12329" class="Symbol">{</a><a id="12330" href="plfa.part1.Relations.html#12330" class="Bound">m</a> <a id="12332" href="plfa.part1.Relations.html#12332" class="Bound">n</a> <a id="12334" class="Symbol">:</a> <a id="12336" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12337" class="Symbol">}</a>
    <a id="12343" class="Symbol">→</a> <a id="12345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12330" class="Bound">m</a> <a id="12347" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="12349" href="plfa.part1.Relations.html#12332" class="Bound">n</a>
      <a id="12357" class="Comment">----------</a>
    <a id="12372" class="Symbol">→</a> <a id="12374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12286" class="Datatype">Total′</a> <a id="12381" href="plfa.part1.Relations.html#12330" class="Bound">m</a> <a id="12383" href="plfa.part1.Relations.html#12332" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12388" class="InductiveConstructor">flipped′</a> <a id="12397" class="Symbol">:</a> <a id="12399" class="Symbol">∀</a> <a id="12401" class="Symbol">{</a><a id="12402" href="plfa.part1.Relations.html#12402" class="Bound">m</a> <a id="12404" href="plfa.part1.Relations.html#12404" class="Bound">n</a> <a id="12406" class="Symbol">:</a> <a id="12408" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12409" class="Symbol">}</a>
    <a id="12415" class="Symbol">→</a> <a id="12417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12404" class="Bound">n</a> <a id="12419" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="12421" href="plfa.part1.Relations.html#12402" class="Bound">m</a>
      <a id="12429" class="Comment">----------</a>
    <a id="12444" class="Symbol">→</a> <a id="12446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12286" class="Datatype">Total′</a> <a id="12453" href="plfa.part1.Relations.html#12402" class="Bound">m</a> <a id="12455" href="plfa.part1.Relations.html#12404" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="12974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12974" class="Function">≤-total</a> <a id="12982" class="Symbol">:</a> <a id="12984" class="Symbol">∀</a> <a id="12986" class="Symbol">(</a><a id="12987" href="plfa.part1.Relations.html#12987" class="Bound">m</a> <a id="12989" href="plfa.part1.Relations.html#12989" class="Bound">n</a> <a id="12991" class="Symbol">:</a> <a id="12993" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12994" class="Symbol">)</a> <a id="12996" class="Symbol">→</a> <a id="12998" href="plfa.part1.Relations.html#11652" class="Datatype">Total</a> <a id="13004" href="plfa.part1.Relations.html#12987" class="Bound">m</a> <a id="13006" href="plfa.part1.Relations.html#12989" class="Bound">n</a>
<a id="13008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12974" class="Function">≤-total</a> <a id="13016" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13024" href="plfa.part1.Relations.html#13024" class="Bound">n</a>                         <a id="13050" class="Symbol">=</a>  <a id="13053" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="13061" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="13065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12974" class="Function">≤-total</a> <a id="13073" class="Symbol">(</a><a id="13074" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13078" href="plfa.part1.Relations.html#13078" class="Bound">m</a><a id="13079" class="Symbol">)</a> <a id="13081" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="13107" class="Symbol">=</a>  <a id="13110" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="13118" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="13122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12974" class="Function">≤-total</a> <a id="13130" class="Symbol">(</a><a id="13131" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13135" href="plfa.part1.Relations.html#13135" class="Bound">m</a><a id="13136" class="Symbol">)</a> <a id="13138" class="Symbol">(</a><a id="13139" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13143" href="plfa.part1.Relations.html#13143" class="Bound">n</a><a id="13144" class="Symbol">)</a> <a id="13146" class="Keyword">with</a> <a id="13151" href="plfa.part1.Relations.html#12974" class="Function">≤-total</a> <a id="13159" href="plfa.part1.Relations.html#13135" class="Bound">m</a> <a id="13161" href="plfa.part1.Relations.html#13143" class="Bound">n</a>
<a id="13163" class="Symbol">...</a>                        <a id="13190" class="Symbol">|</a> <a id="13192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11683" class="InductiveConstructor">forward</a> <a id="13200" href="plfa.part1.Relations.html#13200" class="Bound">m≤n</a>  <a id="13205" class="Symbol">=</a>  <a id="13208" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="13216" class="Symbol">(</a><a id="13217" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="13221" href="plfa.part1.Relations.html#13200" class="Bound">m≤n</a><a id="13224" class="Symbol">)</a>
<a id="13226" class="Symbol">...</a>                        <a id="13253" class="Symbol">|</a> <a id="13255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11740" class="InductiveConstructor">flipped</a> <a id="13263" href="plfa.part1.Relations.html#13263" class="Bound">n≤m</a>  <a id="13268" class="Symbol">=</a>  <a id="13271" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="13279" class="Symbol">(</a><a id="13280" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="13284" href="plfa.part1.Relations.html#13263" class="Bound">n≤m</a><a id="13287" class="Symbol">)</a>
</pre>{% endraw %}In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="14779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14779" class="Function">≤-total′</a> <a id="14788" class="Symbol">:</a> <a id="14790" class="Symbol">∀</a> <a id="14792" class="Symbol">(</a><a id="14793" href="plfa.part1.Relations.html#14793" class="Bound">m</a> <a id="14795" href="plfa.part1.Relations.html#14795" class="Bound">n</a> <a id="14797" class="Symbol">:</a> <a id="14799" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14800" class="Symbol">)</a> <a id="14802" class="Symbol">→</a> <a id="14804" href="plfa.part1.Relations.html#11652" class="Datatype">Total</a> <a id="14810" href="plfa.part1.Relations.html#14793" class="Bound">m</a> <a id="14812" href="plfa.part1.Relations.html#14795" class="Bound">n</a>
<a id="14814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14779" class="Function">≤-total′</a> <a id="14823" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="14831" href="plfa.part1.Relations.html#14831" class="Bound">n</a>        <a id="14840" class="Symbol">=</a>  <a id="14843" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="14851" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="14855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14779" class="Function">≤-total′</a> <a id="14864" class="Symbol">(</a><a id="14865" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14869" href="plfa.part1.Relations.html#14869" class="Bound">m</a><a id="14870" class="Symbol">)</a> <a id="14872" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="14881" class="Symbol">=</a>  <a id="14884" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="14892" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="14896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14779" class="Function">≤-total′</a> <a id="14905" class="Symbol">(</a><a id="14906" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14910" href="plfa.part1.Relations.html#14910" class="Bound">m</a><a id="14911" class="Symbol">)</a> <a id="14913" class="Symbol">(</a><a id="14914" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14918" href="plfa.part1.Relations.html#14918" class="Bound">n</a><a id="14919" class="Symbol">)</a>  <a id="14922" class="Symbol">=</a>  <a id="14925" href="plfa.part1.Relations.html#14957" class="Function">helper</a> <a id="14932" class="Symbol">(</a><a id="14933" href="plfa.part1.Relations.html#14779" class="Function">≤-total′</a> <a id="14942" href="plfa.part1.Relations.html#14910" class="Bound">m</a> <a id="14944" href="plfa.part1.Relations.html#14918" class="Bound">n</a><a id="14945" class="Symbol">)</a>
  <a id="14949" class="Keyword">where</a>
  <a id="14957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14957" class="Function">helper</a> <a id="14964" class="Symbol">:</a> <a id="14966" href="plfa.part1.Relations.html#11652" class="Datatype">Total</a> <a id="14972" href="plfa.part1.Relations.html#14910" class="Bound">m</a> <a id="14974" href="plfa.part1.Relations.html#14918" class="Bound">n</a> <a id="14976" class="Symbol">→</a> <a id="14978" href="plfa.part1.Relations.html#11652" class="Datatype">Total</a> <a id="14984" class="Symbol">(</a><a id="14985" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14989" href="plfa.part1.Relations.html#14910" class="Bound">m</a><a id="14990" class="Symbol">)</a> <a id="14992" class="Symbol">(</a><a id="14993" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14997" href="plfa.part1.Relations.html#14918" class="Bound">n</a><a id="14998" class="Symbol">)</a>
  <a id="15002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14957" class="Function">helper</a> <a id="15009" class="Symbol">(</a><a id="15010" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="15018" href="plfa.part1.Relations.html#15018" class="Bound">m≤n</a><a id="15021" class="Symbol">)</a>  <a id="15024" class="Symbol">=</a>  <a id="15027" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="15035" class="Symbol">(</a><a id="15036" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15040" href="plfa.part1.Relations.html#15018" class="Bound">m≤n</a><a id="15043" class="Symbol">)</a>
  <a id="15047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14957" class="Function">helper</a> <a id="15054" class="Symbol">(</a><a id="15055" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="15063" href="plfa.part1.Relations.html#15063" class="Bound">n≤m</a><a id="15066" class="Symbol">)</a>  <a id="15069" class="Symbol">=</a>  <a id="15072" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="15080" class="Symbol">(</a><a id="15081" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15085" href="plfa.part1.Relations.html#15063" class="Bound">n≤m</a><a id="15088" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="15710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15710" class="Function">≤-total″</a> <a id="15719" class="Symbol">:</a> <a id="15721" class="Symbol">∀</a> <a id="15723" class="Symbol">(</a><a id="15724" href="plfa.part1.Relations.html#15724" class="Bound">m</a> <a id="15726" href="plfa.part1.Relations.html#15726" class="Bound">n</a> <a id="15728" class="Symbol">:</a> <a id="15730" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15731" class="Symbol">)</a> <a id="15733" class="Symbol">→</a> <a id="15735" href="plfa.part1.Relations.html#11652" class="Datatype">Total</a> <a id="15741" href="plfa.part1.Relations.html#15724" class="Bound">m</a> <a id="15743" href="plfa.part1.Relations.html#15726" class="Bound">n</a>
<a id="15745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15710" class="Function">≤-total″</a> <a id="15754" href="plfa.part1.Relations.html#15754" class="Bound">m</a>       <a id="15762" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="15788" class="Symbol">=</a>  <a id="15791" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="15799" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="15803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15710" class="Function">≤-total″</a> <a id="15812" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15820" class="Symbol">(</a><a id="15821" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15825" href="plfa.part1.Relations.html#15825" class="Bound">n</a><a id="15826" class="Symbol">)</a>                   <a id="15846" class="Symbol">=</a>  <a id="15849" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="15857" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="15861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15710" class="Function">≤-total″</a> <a id="15870" class="Symbol">(</a><a id="15871" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15875" href="plfa.part1.Relations.html#15875" class="Bound">m</a><a id="15876" class="Symbol">)</a> <a id="15878" class="Symbol">(</a><a id="15879" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15883" href="plfa.part1.Relations.html#15883" class="Bound">n</a><a id="15884" class="Symbol">)</a> <a id="15886" class="Keyword">with</a> <a id="15891" href="plfa.part1.Relations.html#15710" class="Function">≤-total″</a> <a id="15900" href="plfa.part1.Relations.html#15875" class="Bound">m</a> <a id="15902" href="plfa.part1.Relations.html#15883" class="Bound">n</a>
<a id="15904" class="Symbol">...</a>                        <a id="15931" class="Symbol">|</a> <a id="15933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11683" class="InductiveConstructor">forward</a> <a id="15941" href="plfa.part1.Relations.html#15941" class="Bound">m≤n</a>   <a id="15947" class="Symbol">=</a>  <a id="15950" href="plfa.part1.Relations.html#11683" class="InductiveConstructor">forward</a> <a id="15958" class="Symbol">(</a><a id="15959" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15963" href="plfa.part1.Relations.html#15941" class="Bound">m≤n</a><a id="15966" class="Symbol">)</a>
<a id="15968" class="Symbol">...</a>                        <a id="15995" class="Symbol">|</a> <a id="15997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11740" class="InductiveConstructor">flipped</a> <a id="16005" href="plfa.part1.Relations.html#16005" class="Bound">n≤m</a>   <a id="16011" class="Symbol">=</a>  <a id="16014" href="plfa.part1.Relations.html#11740" class="InductiveConstructor">flipped</a> <a id="16022" class="Symbol">(</a><a id="16023" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="16027" href="plfa.part1.Relations.html#16005" class="Bound">n≤m</a><a id="16030" class="Symbol">)</a>
</pre>{% endraw %}It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="16619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16619" class="Function">+-monoʳ-≤</a> <a id="16629" class="Symbol">:</a> <a id="16631" class="Symbol">∀</a> <a id="16633" class="Symbol">(</a><a id="16634" href="plfa.part1.Relations.html#16634" class="Bound">n</a> <a id="16636" href="plfa.part1.Relations.html#16636" class="Bound">p</a> <a id="16638" href="plfa.part1.Relations.html#16638" class="Bound">q</a> <a id="16640" class="Symbol">:</a> <a id="16642" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16643" class="Symbol">)</a>
  <a id="16647" class="Symbol">→</a> <a id="16649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16636" class="Bound">p</a> <a id="16651" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="16653" href="plfa.part1.Relations.html#16638" class="Bound">q</a>
    <a id="16659" class="Comment">-------------</a>
  <a id="16675" class="Symbol">→</a> <a id="16677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16634" class="Bound">n</a> <a id="16679" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16681" href="plfa.part1.Relations.html#16636" class="Bound">p</a> <a id="16683" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="16685" href="plfa.part1.Relations.html#16634" class="Bound">n</a> <a id="16687" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16689" href="plfa.part1.Relations.html#16638" class="Bound">q</a>
<a id="16691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16619" class="Function">+-monoʳ-≤</a> <a id="16701" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16709" href="plfa.part1.Relations.html#16709" class="Bound">p</a> <a id="16711" href="plfa.part1.Relations.html#16711" class="Bound">q</a> <a id="16713" href="plfa.part1.Relations.html#16713" class="Bound">p≤q</a>  <a id="16718" class="Symbol">=</a>  <a id="16721" href="plfa.part1.Relations.html#16713" class="Bound">p≤q</a>
<a id="16725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16619" class="Function">+-monoʳ-≤</a> <a id="16735" class="Symbol">(</a><a id="16736" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16740" href="plfa.part1.Relations.html#16740" class="Bound">n</a><a id="16741" class="Symbol">)</a> <a id="16743" href="plfa.part1.Relations.html#16743" class="Bound">p</a> <a id="16745" href="plfa.part1.Relations.html#16745" class="Bound">q</a> <a id="16747" href="plfa.part1.Relations.html#16747" class="Bound">p≤q</a>  <a id="16752" class="Symbol">=</a>  <a id="16755" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="16759" class="Symbol">(</a><a id="16760" href="plfa.part1.Relations.html#16619" class="Function">+-monoʳ-≤</a> <a id="16770" href="plfa.part1.Relations.html#16740" class="Bound">n</a> <a id="16772" href="plfa.part1.Relations.html#16743" class="Bound">p</a> <a id="16774" href="plfa.part1.Relations.html#16745" class="Bound">q</a> <a id="16776" href="plfa.part1.Relations.html#16747" class="Bound">p≤q</a><a id="16779" class="Symbol">)</a>
</pre>{% endraw %}The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17419" class="Function">+-monoˡ-≤</a> <a id="17429" class="Symbol">:</a> <a id="17431" class="Symbol">∀</a> <a id="17433" class="Symbol">(</a><a id="17434" href="plfa.part1.Relations.html#17434" class="Bound">m</a> <a id="17436" href="plfa.part1.Relations.html#17436" class="Bound">n</a> <a id="17438" href="plfa.part1.Relations.html#17438" class="Bound">p</a> <a id="17440" class="Symbol">:</a> <a id="17442" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17443" class="Symbol">)</a>
  <a id="17447" class="Symbol">→</a> <a id="17449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17434" class="Bound">m</a> <a id="17451" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17453" href="plfa.part1.Relations.html#17436" class="Bound">n</a>
    <a id="17459" class="Comment">-------------</a>
  <a id="17475" class="Symbol">→</a> <a id="17477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17434" class="Bound">m</a> <a id="17479" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17481" href="plfa.part1.Relations.html#17438" class="Bound">p</a> <a id="17483" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17485" href="plfa.part1.Relations.html#17436" class="Bound">n</a> <a id="17487" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17489" href="plfa.part1.Relations.html#17438" class="Bound">p</a>
<a id="17491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17419" class="Function">+-monoˡ-≤</a> <a id="17501" href="plfa.part1.Relations.html#17501" class="Bound">m</a> <a id="17503" href="plfa.part1.Relations.html#17503" class="Bound">n</a> <a id="17505" href="plfa.part1.Relations.html#17505" class="Bound">p</a> <a id="17507" href="plfa.part1.Relations.html#17507" class="Bound">m≤n</a>  <a id="17512" class="Keyword">rewrite</a> <a id="17520" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17527" href="plfa.part1.Relations.html#17501" class="Bound">m</a> <a id="17529" href="plfa.part1.Relations.html#17505" class="Bound">p</a> <a id="17531" class="Symbol">|</a> <a id="17533" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17540" href="plfa.part1.Relations.html#17503" class="Bound">n</a> <a id="17542" href="plfa.part1.Relations.html#17505" class="Bound">p</a>  <a id="17545" class="Symbol">=</a> <a id="17547" href="plfa.part1.Relations.html#16619" class="Function">+-monoʳ-≤</a> <a id="17557" href="plfa.part1.Relations.html#17505" class="Bound">p</a> <a id="17559" href="plfa.part1.Relations.html#17501" class="Bound">m</a> <a id="17561" href="plfa.part1.Relations.html#17503" class="Bound">n</a> <a id="17563" href="plfa.part1.Relations.html#17507" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="17761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17761" class="Function">+-mono-≤</a> <a id="17770" class="Symbol">:</a> <a id="17772" class="Symbol">∀</a> <a id="17774" class="Symbol">(</a><a id="17775" href="plfa.part1.Relations.html#17775" class="Bound">m</a> <a id="17777" href="plfa.part1.Relations.html#17777" class="Bound">n</a> <a id="17779" href="plfa.part1.Relations.html#17779" class="Bound">p</a> <a id="17781" href="plfa.part1.Relations.html#17781" class="Bound">q</a> <a id="17783" class="Symbol">:</a> <a id="17785" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17786" class="Symbol">)</a>
  <a id="17790" class="Symbol">→</a> <a id="17792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17775" class="Bound">m</a> <a id="17794" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17796" href="plfa.part1.Relations.html#17777" class="Bound">n</a>
  <a id="17800" class="Symbol">→</a> <a id="17802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17779" class="Bound">p</a> <a id="17804" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17806" href="plfa.part1.Relations.html#17781" class="Bound">q</a>
    <a id="17812" class="Comment">-------------</a>
  <a id="17828" class="Symbol">→</a> <a id="17830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17775" class="Bound">m</a> <a id="17832" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17834" href="plfa.part1.Relations.html#17779" class="Bound">p</a> <a id="17836" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17838" href="plfa.part1.Relations.html#17777" class="Bound">n</a> <a id="17840" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17842" href="plfa.part1.Relations.html#17781" class="Bound">q</a>
<a id="17844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17761" class="Function">+-mono-≤</a> <a id="17853" href="plfa.part1.Relations.html#17853" class="Bound">m</a> <a id="17855" href="plfa.part1.Relations.html#17855" class="Bound">n</a> <a id="17857" href="plfa.part1.Relations.html#17857" class="Bound">p</a> <a id="17859" href="plfa.part1.Relations.html#17859" class="Bound">q</a> <a id="17861" href="plfa.part1.Relations.html#17861" class="Bound">m≤n</a> <a id="17865" href="plfa.part1.Relations.html#17865" class="Bound">p≤q</a>  <a id="17870" class="Symbol">=</a>  <a id="17873" href="plfa.part1.Relations.html#8355" class="Function">≤-trans</a> <a id="17881" class="Symbol">(</a><a id="17882" href="plfa.part1.Relations.html#17419" class="Function">+-monoˡ-≤</a> <a id="17892" href="plfa.part1.Relations.html#17853" class="Bound">m</a> <a id="17894" href="plfa.part1.Relations.html#17855" class="Bound">n</a> <a id="17896" href="plfa.part1.Relations.html#17857" class="Bound">p</a> <a id="17898" href="plfa.part1.Relations.html#17861" class="Bound">m≤n</a><a id="17901" class="Symbol">)</a> <a id="17903" class="Symbol">(</a><a id="17904" href="plfa.part1.Relations.html#16619" class="Function">+-monoʳ-≤</a> <a id="17914" href="plfa.part1.Relations.html#17855" class="Bound">n</a> <a id="17916" href="plfa.part1.Relations.html#17857" class="Bound">p</a> <a id="17918" href="plfa.part1.Relations.html#17859" class="Bound">q</a> <a id="17920" href="plfa.part1.Relations.html#17865" class="Bound">p≤q</a><a id="17923" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="18232" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18365" class="Keyword">infix</a> <a id="18371" class="Number">4</a> <a id="18373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Datatype Operator">_&lt;_</a>

<a id="18378" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Datatype Operator">_&lt;_</a> <a id="18387" class="Symbol">:</a> <a id="18389" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18391" class="Symbol">→</a> <a id="18393" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18395" class="Symbol">→</a> <a id="18397" class="PrimitiveType">Set</a> <a id="18401" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18410" class="InductiveConstructor">z&lt;s</a> <a id="18414" class="Symbol">:</a> <a id="18416" class="Symbol">∀</a> <a id="18418" class="Symbol">{</a><a id="18419" href="plfa.part1.Relations.html#18419" class="Bound">n</a> <a id="18421" class="Symbol">:</a> <a id="18423" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18424" class="Symbol">}</a>
      <a id="18432" class="Comment">------------</a>
    <a id="18449" class="Symbol">→</a> <a id="18451" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Datatype Operator">&lt;</a> <a id="18458" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18462" href="plfa.part1.Relations.html#18419" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18467" class="InductiveConstructor">s&lt;s</a> <a id="18471" class="Symbol">:</a> <a id="18473" class="Symbol">∀</a> <a id="18475" class="Symbol">{</a><a id="18476" href="plfa.part1.Relations.html#18476" class="Bound">m</a> <a id="18478" href="plfa.part1.Relations.html#18478" class="Bound">n</a> <a id="18480" class="Symbol">:</a> <a id="18482" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18483" class="Symbol">}</a>
    <a id="18489" class="Symbol">→</a> <a id="18491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18476" class="Bound">m</a> <a id="18493" href="plfa.part1.Relations.html#18383" class="Datatype Operator">&lt;</a> <a id="18495" href="plfa.part1.Relations.html#18478" class="Bound">n</a>
      <a id="18503" class="Comment">-------------</a>
    <a id="18521" class="Symbol">→</a> <a id="18523" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18476" class="Bound">m</a> <a id="18529" href="plfa.part1.Relations.html#18383" class="Datatype Operator">&lt;</a> <a id="18531" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18535" href="plfa.part1.Relations.html#18478" class="Bound">n</a>
</pre>{% endraw %}The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

{% raw %}<pre class="Agda"><a id="19704" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

{% raw %}<pre class="Agda"><a id="20203" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20423" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="20566" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="20837" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="21076" class="Keyword">data</a> <a id="even"></a><a id="21081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="21086" class="Symbol">:</a> <a id="21088" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21090" class="Symbol">→</a> <a id="21092" class="PrimitiveType">Set</a>
<a id="21096" class="Keyword">data</a> <a id="odd"></a><a id="21101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a>  <a id="21106" class="Symbol">:</a> <a id="21108" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21110" class="Symbol">→</a> <a id="21112" class="PrimitiveType">Set</a>

<a id="21117" class="Keyword">data</a> <a id="21122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="21127" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21136" class="InductiveConstructor">zero</a> <a id="21141" class="Symbol">:</a>
      <a id="21149" class="Comment">---------</a>
      <a id="21165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="21170" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21178" class="InductiveConstructor">suc</a>  <a id="21183" class="Symbol">:</a> <a id="21185" class="Symbol">∀</a> <a id="21187" class="Symbol">{</a><a id="21188" href="plfa.part1.Relations.html#21188" class="Bound">n</a> <a id="21190" class="Symbol">:</a> <a id="21192" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21193" class="Symbol">}</a>
    <a id="21199" class="Symbol">→</a> <a id="21201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a> <a id="21205" href="plfa.part1.Relations.html#21188" class="Bound">n</a>
      <a id="21213" class="Comment">------------</a>
    <a id="21230" class="Symbol">→</a> <a id="21232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="21237" class="Symbol">(</a><a id="21238" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21242" href="plfa.part1.Relations.html#21188" class="Bound">n</a><a id="21243" class="Symbol">)</a>

<a id="21246" class="Keyword">data</a> <a id="21251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a> <a id="21255" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21264" class="InductiveConstructor">suc</a>   <a id="21270" class="Symbol">:</a> <a id="21272" class="Symbol">∀</a> <a id="21274" class="Symbol">{</a><a id="21275" href="plfa.part1.Relations.html#21275" class="Bound">n</a> <a id="21277" class="Symbol">:</a> <a id="21279" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21280" class="Symbol">}</a>
    <a id="21286" class="Symbol">→</a> <a id="21288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="21293" href="plfa.part1.Relations.html#21275" class="Bound">n</a>
      <a id="21301" class="Comment">-----------</a>
    <a id="21317" class="Symbol">→</a> <a id="21319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a> <a id="21323" class="Symbol">(</a><a id="21324" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21328" href="plfa.part1.Relations.html#21275" class="Bound">n</a><a id="21329" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="22489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22489" class="Function">e+e≡e</a> <a id="22495" class="Symbol">:</a> <a id="22497" class="Symbol">∀</a> <a id="22499" class="Symbol">{</a><a id="22500" href="plfa.part1.Relations.html#22500" class="Bound">m</a> <a id="22502" href="plfa.part1.Relations.html#22502" class="Bound">n</a> <a id="22504" class="Symbol">:</a> <a id="22506" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22507" class="Symbol">}</a>
  <a id="22511" class="Symbol">→</a> <a id="22513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="22518" href="plfa.part1.Relations.html#22500" class="Bound">m</a>
  <a id="22522" class="Symbol">→</a> <a id="22524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="22529" href="plfa.part1.Relations.html#22502" class="Bound">n</a>
    <a id="22535" class="Comment">------------</a>
  <a id="22550" class="Symbol">→</a> <a id="22552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="22557" class="Symbol">(</a><a id="22558" href="plfa.part1.Relations.html#22500" class="Bound">m</a> <a id="22560" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22562" href="plfa.part1.Relations.html#22502" class="Bound">n</a><a id="22563" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22566" class="Function">o+e≡o</a> <a id="22572" class="Symbol">:</a> <a id="22574" class="Symbol">∀</a> <a id="22576" class="Symbol">{</a><a id="22577" href="plfa.part1.Relations.html#22577" class="Bound">m</a> <a id="22579" href="plfa.part1.Relations.html#22579" class="Bound">n</a> <a id="22581" class="Symbol">:</a> <a id="22583" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22584" class="Symbol">}</a>
  <a id="22588" class="Symbol">→</a> <a id="22590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a> <a id="22594" href="plfa.part1.Relations.html#22577" class="Bound">m</a>
  <a id="22598" class="Symbol">→</a> <a id="22600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21081" class="Datatype">even</a> <a id="22605" href="plfa.part1.Relations.html#22579" class="Bound">n</a>
    <a id="22611" class="Comment">-----------</a>
  <a id="22625" class="Symbol">→</a> <a id="22627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21101" class="Datatype">odd</a> <a id="22631" class="Symbol">(</a><a id="22632" href="plfa.part1.Relations.html#22577" class="Bound">m</a> <a id="22634" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22636" href="plfa.part1.Relations.html#22579" class="Bound">n</a><a id="22637" class="Symbol">)</a>

<a id="22640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22489" class="Function">e+e≡e</a> <a id="22646" href="plfa.part1.Relations.html#21136" class="InductiveConstructor">zero</a>     <a id="22655" href="plfa.part1.Relations.html#22655" class="Bound">en</a>  <a id="22659" class="Symbol">=</a>  <a id="22662" href="plfa.part1.Relations.html#22655" class="Bound">en</a>
<a id="22665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22489" class="Function">e+e≡e</a> <a id="22671" class="Symbol">(</a><a id="22672" href="plfa.part1.Relations.html#21178" class="InductiveConstructor">suc</a> <a id="22676" href="plfa.part1.Relations.html#22676" class="Bound">om</a><a id="22678" class="Symbol">)</a> <a id="22680" href="plfa.part1.Relations.html#22680" class="Bound">en</a>  <a id="22684" class="Symbol">=</a>  <a id="22687" href="plfa.part1.Relations.html#21178" class="InductiveConstructor">suc</a> <a id="22691" class="Symbol">(</a><a id="22692" href="plfa.part1.Relations.html#22566" class="Function">o+e≡o</a> <a id="22698" href="plfa.part1.Relations.html#22676" class="Bound">om</a> <a id="22701" href="plfa.part1.Relations.html#22680" class="Bound">en</a><a id="22703" class="Symbol">)</a>

<a id="22706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22566" class="Function">o+e≡o</a> <a id="22712" class="Symbol">(</a><a id="22713" href="plfa.part1.Relations.html#21264" class="InductiveConstructor">suc</a> <a id="22717" href="plfa.part1.Relations.html#22717" class="Bound">em</a><a id="22719" class="Symbol">)</a> <a id="22721" href="plfa.part1.Relations.html#22721" class="Bound">en</a>  <a id="22725" class="Symbol">=</a>  <a id="22728" href="plfa.part1.Relations.html#21264" class="InductiveConstructor">suc</a> <a id="22732" class="Symbol">(</a><a id="22733" href="plfa.part1.Relations.html#22489" class="Function">e+e≡e</a> <a id="22739" href="plfa.part1.Relations.html#22717" class="Bound">em</a> <a id="22742" href="plfa.part1.Relations.html#22721" class="Bound">en</a><a id="22744" class="Symbol">)</a>
</pre>{% endraw %}Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

{% raw %}<pre class="Agda"><a id="23882" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

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

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

{% raw %}<pre class="Agda"><a id="25259" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25395" class="Keyword">import</a> <a id="25402" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25411" class="Keyword">using</a> <a id="25417" class="Symbol">(</a><a id="25418" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25421" class="Symbol">;</a> <a id="25423" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25426" class="Symbol">;</a> <a id="25428" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25431" class="Symbol">)</a>
<a id="25433" class="Keyword">import</a> <a id="25440" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25460" class="Keyword">using</a> <a id="25466" class="Symbol">(</a><a id="25467" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25473" class="Symbol">;</a> <a id="25475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="25482" class="Symbol">;</a> <a id="25484" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="25493" class="Symbol">;</a> <a id="25495" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="25502" class="Symbol">;</a>
                                  <a id="25538" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="25547" class="Symbol">;</a> <a id="25549" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="25558" class="Symbol">;</a> <a id="25560" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="25568" class="Symbol">)</a>
</pre>{% endraw %}In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
