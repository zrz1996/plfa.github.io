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

In our defintions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5071" class="Function">inv-s≤s</a> <a id="5079" class="Symbol">:</a> <a id="5081" class="Symbol">∀</a> <a id="5083" class="Symbol">{</a><a id="5084" href="plfa.part1.Relations.html#5084" class="Bound">m</a> <a id="5086" href="plfa.part1.Relations.html#5086" class="Bound">n</a> <a id="5088" class="Symbol">:</a> <a id="5090" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5091" class="Symbol">}</a>
  <a id="5095" class="Symbol">→</a> <a id="5097" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5084" class="Bound">m</a> <a id="5103" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5105" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5109" href="plfa.part1.Relations.html#5086" class="Bound">n</a>
    <a id="5115" class="Comment">-------------</a>
  <a id="5131" class="Symbol">→</a> <a id="5133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5084" class="Bound">m</a> <a id="5135" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5137" href="plfa.part1.Relations.html#5086" class="Bound">n</a>
<a id="5139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5071" class="Function">inv-s≤s</a> <a id="5147" class="Symbol">(</a><a id="5148" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="5152" href="plfa.part1.Relations.html#5152" class="Bound">m≤n</a><a id="5155" class="Symbol">)</a> <a id="5157" class="Symbol">=</a> <a id="5159" href="plfa.part1.Relations.html#5152" class="Bound">m≤n</a>
</pre>{% endraw %}Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to choose derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="5674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5674" class="Function">inv-z≤n</a> <a id="5682" class="Symbol">:</a> <a id="5684" class="Symbol">∀</a> <a id="5686" class="Symbol">{</a><a id="5687" href="plfa.part1.Relations.html#5687" class="Bound">m</a> <a id="5689" class="Symbol">:</a> <a id="5691" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5692" class="Symbol">}</a>
  <a id="5696" class="Symbol">→</a> <a id="5698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5687" class="Bound">m</a> <a id="5700" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="5702" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="5711" class="Comment">--------</a>
  <a id="5722" class="Symbol">→</a> <a id="5724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5687" class="Bound">m</a> <a id="5726" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5728" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="5733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5674" class="Function">inv-z≤n</a> <a id="5741" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a> <a id="5745" class="Symbol">=</a> <a id="5747" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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

{% raw %}<pre class="Agda"><a id="7249" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7344" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="7644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7644" class="Function">≤-refl</a> <a id="7651" class="Symbol">:</a> <a id="7653" class="Symbol">∀</a> <a id="7655" class="Symbol">{</a><a id="7656" href="plfa.part1.Relations.html#7656" class="Bound">n</a> <a id="7658" class="Symbol">:</a> <a id="7660" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7661" class="Symbol">}</a>
    <a id="7667" class="Comment">-----</a>
  <a id="7675" class="Symbol">→</a> <a id="7677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7656" class="Bound">n</a> <a id="7679" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="7681" href="plfa.part1.Relations.html#7656" class="Bound">n</a>
<a id="7683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7644" class="Function">≤-refl</a> <a id="7690" class="Symbol">{</a><a id="7691" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="7695" class="Symbol">}</a> <a id="7697" class="Symbol">=</a> <a id="7699" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="7703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#7644" class="Function">≤-refl</a> <a id="7710" class="Symbol">{</a><a id="7711" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7715" href="plfa.part1.Relations.html#7715" class="Bound">n</a><a id="7716" class="Symbol">}</a> <a id="7718" class="Symbol">=</a> <a id="7720" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="7724" href="plfa.part1.Relations.html#7644" class="Function">≤-refl</a>
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
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8361" class="Function">≤-trans</a> <a id="8369" class="Symbol">:</a> <a id="8371" class="Symbol">∀</a> <a id="8373" class="Symbol">{</a><a id="8374" href="plfa.part1.Relations.html#8374" class="Bound">m</a> <a id="8376" href="plfa.part1.Relations.html#8376" class="Bound">n</a> <a id="8378" href="plfa.part1.Relations.html#8378" class="Bound">p</a> <a id="8380" class="Symbol">:</a> <a id="8382" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8383" class="Symbol">}</a>
  <a id="8387" class="Symbol">→</a> <a id="8389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8374" class="Bound">m</a> <a id="8391" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8393" href="plfa.part1.Relations.html#8376" class="Bound">n</a>
  <a id="8397" class="Symbol">→</a> <a id="8399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8376" class="Bound">n</a> <a id="8401" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8403" href="plfa.part1.Relations.html#8378" class="Bound">p</a>
    <a id="8409" class="Comment">-----</a>
  <a id="8417" class="Symbol">→</a> <a id="8419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8374" class="Bound">m</a> <a id="8421" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="8423" href="plfa.part1.Relations.html#8378" class="Bound">p</a>
<a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8361" class="Function">≤-trans</a> <a id="8433" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="8443" class="Symbol">_</a>          <a id="8454" class="Symbol">=</a>  <a id="8457" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="8461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8361" class="Function">≤-trans</a> <a id="8469" class="Symbol">(</a><a id="8470" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8474" href="plfa.part1.Relations.html#8474" class="Bound">m≤n</a><a id="8477" class="Symbol">)</a> <a id="8479" class="Symbol">(</a><a id="8480" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8484" href="plfa.part1.Relations.html#8484" class="Bound">n≤p</a><a id="8487" class="Symbol">)</a>  <a id="8490" class="Symbol">=</a>  <a id="8493" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="8497" class="Symbol">(</a><a id="8498" href="plfa.part1.Relations.html#8361" class="Function">≤-trans</a> <a id="8506" href="plfa.part1.Relations.html#8474" class="Bound">m≤n</a> <a id="8510" href="plfa.part1.Relations.html#8484" class="Bound">n≤p</a><a id="8513" class="Symbol">)</a>
</pre>{% endraw %}Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
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
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9474" class="Function">≤-trans′</a> <a id="9483" class="Symbol">:</a> <a id="9485" class="Symbol">∀</a> <a id="9487" class="Symbol">(</a><a id="9488" href="plfa.part1.Relations.html#9488" class="Bound">m</a> <a id="9490" href="plfa.part1.Relations.html#9490" class="Bound">n</a> <a id="9492" href="plfa.part1.Relations.html#9492" class="Bound">p</a> <a id="9494" class="Symbol">:</a> <a id="9496" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9497" class="Symbol">)</a>
  <a id="9501" class="Symbol">→</a> <a id="9503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9488" class="Bound">m</a> <a id="9505" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9507" href="plfa.part1.Relations.html#9490" class="Bound">n</a>
  <a id="9511" class="Symbol">→</a> <a id="9513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9490" class="Bound">n</a> <a id="9515" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9517" href="plfa.part1.Relations.html#9492" class="Bound">p</a>
    <a id="9523" class="Comment">-----</a>
  <a id="9531" class="Symbol">→</a> <a id="9533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9488" class="Bound">m</a> <a id="9535" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="9537" href="plfa.part1.Relations.html#9492" class="Bound">p</a>
<a id="9539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9474" class="Function">≤-trans′</a> <a id="9548" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="9556" class="Symbol">_</a>       <a id="9564" class="Symbol">_</a>       <a id="9572" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="9582" class="Symbol">_</a>          <a id="9593" class="Symbol">=</a>  <a id="9596" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="9600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9474" class="Function">≤-trans′</a> <a id="9609" class="Symbol">(</a><a id="9610" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9614" href="plfa.part1.Relations.html#9614" class="Bound">m</a><a id="9615" class="Symbol">)</a> <a id="9617" class="Symbol">(</a><a id="9618" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9622" href="plfa.part1.Relations.html#9622" class="Bound">n</a><a id="9623" class="Symbol">)</a> <a id="9625" class="Symbol">(</a><a id="9626" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9630" href="plfa.part1.Relations.html#9630" class="Bound">p</a><a id="9631" class="Symbol">)</a> <a id="9633" class="Symbol">(</a><a id="9634" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9638" href="plfa.part1.Relations.html#9638" class="Bound">m≤n</a><a id="9641" class="Symbol">)</a> <a id="9643" class="Symbol">(</a><a id="9644" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9648" href="plfa.part1.Relations.html#9648" class="Bound">n≤p</a><a id="9651" class="Symbol">)</a>  <a id="9654" class="Symbol">=</a>  <a id="9657" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="9661" class="Symbol">(</a><a id="9662" href="plfa.part1.Relations.html#9474" class="Function">≤-trans′</a> <a id="9671" href="plfa.part1.Relations.html#9614" class="Bound">m</a> <a id="9673" href="plfa.part1.Relations.html#9622" class="Bound">n</a> <a id="9675" href="plfa.part1.Relations.html#9630" class="Bound">p</a> <a id="9677" href="plfa.part1.Relations.html#9638" class="Bound">m≤n</a> <a id="9681" href="plfa.part1.Relations.html#9648" class="Bound">n≤p</a><a id="9684" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10429" class="Function">≤-antisym</a> <a id="10439" class="Symbol">:</a> <a id="10441" class="Symbol">∀</a> <a id="10443" class="Symbol">{</a><a id="10444" href="plfa.part1.Relations.html#10444" class="Bound">m</a> <a id="10446" href="plfa.part1.Relations.html#10446" class="Bound">n</a> <a id="10448" class="Symbol">:</a> <a id="10450" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10451" class="Symbol">}</a>
  <a id="10455" class="Symbol">→</a> <a id="10457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10444" class="Bound">m</a> <a id="10459" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="10461" href="plfa.part1.Relations.html#10446" class="Bound">n</a>
  <a id="10465" class="Symbol">→</a> <a id="10467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10446" class="Bound">n</a> <a id="10469" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="10471" href="plfa.part1.Relations.html#10444" class="Bound">m</a>
    <a id="10477" class="Comment">-----</a>
  <a id="10485" class="Symbol">→</a> <a id="10487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10444" class="Bound">m</a> <a id="10489" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10491" href="plfa.part1.Relations.html#10446" class="Bound">n</a>
<a id="10493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10429" class="Function">≤-antisym</a> <a id="10503" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>       <a id="10513" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>        <a id="10524" class="Symbol">=</a>  <a id="10527" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="10532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10429" class="Function">≤-antisym</a> <a id="10542" class="Symbol">(</a><a id="10543" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="10547" href="plfa.part1.Relations.html#10547" class="Bound">m≤n</a><a id="10550" class="Symbol">)</a> <a id="10552" class="Symbol">(</a><a id="10553" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="10557" href="plfa.part1.Relations.html#10557" class="Bound">n≤m</a><a id="10560" class="Symbol">)</a>  <a id="10563" class="Symbol">=</a>  <a id="10566" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10571" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10575" class="Symbol">(</a><a id="10576" href="plfa.part1.Relations.html#10429" class="Function">≤-antisym</a> <a id="10586" href="plfa.part1.Relations.html#10547" class="Bound">m≤n</a> <a id="10590" href="plfa.part1.Relations.html#10557" class="Bound">n≤m</a><a id="10593" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="11399" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="11653" class="Keyword">data</a> <a id="Total"></a><a id="11658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11658" class="Datatype">Total</a> <a id="11664" class="Symbol">(</a><a id="11665" href="plfa.part1.Relations.html#11665" class="Bound">m</a> <a id="11667" href="plfa.part1.Relations.html#11667" class="Bound">n</a> <a id="11669" class="Symbol">:</a> <a id="11671" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11672" class="Symbol">)</a> <a id="11674" class="Symbol">:</a> <a id="11676" class="PrimitiveType">Set</a> <a id="11680" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11689" class="InductiveConstructor">forward</a> <a id="11697" class="Symbol">:</a>
      <a id="11705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11665" class="Bound">m</a> <a id="11707" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="11709" href="plfa.part1.Relations.html#11667" class="Bound">n</a>
      <a id="11717" class="Comment">---------</a>
    <a id="11731" class="Symbol">→</a> <a id="11733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11658" class="Datatype">Total</a> <a id="11739" href="plfa.part1.Relations.html#11665" class="Bound">m</a> <a id="11741" href="plfa.part1.Relations.html#11667" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11746" class="InductiveConstructor">flipped</a> <a id="11754" class="Symbol">:</a>
      <a id="11762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11667" class="Bound">n</a> <a id="11764" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="11766" href="plfa.part1.Relations.html#11665" class="Bound">m</a>
      <a id="11774" class="Comment">---------</a>
    <a id="11788" class="Symbol">→</a> <a id="11790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11658" class="Datatype">Total</a> <a id="11796" href="plfa.part1.Relations.html#11665" class="Bound">m</a> <a id="11798" href="plfa.part1.Relations.html#11667" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12287" class="Keyword">data</a> <a id="Total′"></a><a id="12292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12292" class="Datatype">Total′</a> <a id="12299" class="Symbol">:</a> <a id="12301" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12303" class="Symbol">→</a> <a id="12305" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12307" class="Symbol">→</a> <a id="12309" class="PrimitiveType">Set</a> <a id="12313" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12322" class="InductiveConstructor">forward′</a> <a id="12331" class="Symbol">:</a> <a id="12333" class="Symbol">∀</a> <a id="12335" class="Symbol">{</a><a id="12336" href="plfa.part1.Relations.html#12336" class="Bound">m</a> <a id="12338" href="plfa.part1.Relations.html#12338" class="Bound">n</a> <a id="12340" class="Symbol">:</a> <a id="12342" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12343" class="Symbol">}</a>
    <a id="12349" class="Symbol">→</a> <a id="12351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12336" class="Bound">m</a> <a id="12353" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="12355" href="plfa.part1.Relations.html#12338" class="Bound">n</a>
      <a id="12363" class="Comment">----------</a>
    <a id="12378" class="Symbol">→</a> <a id="12380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12292" class="Datatype">Total′</a> <a id="12387" href="plfa.part1.Relations.html#12336" class="Bound">m</a> <a id="12389" href="plfa.part1.Relations.html#12338" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12394" class="InductiveConstructor">flipped′</a> <a id="12403" class="Symbol">:</a> <a id="12405" class="Symbol">∀</a> <a id="12407" class="Symbol">{</a><a id="12408" href="plfa.part1.Relations.html#12408" class="Bound">m</a> <a id="12410" href="plfa.part1.Relations.html#12410" class="Bound">n</a> <a id="12412" class="Symbol">:</a> <a id="12414" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12415" class="Symbol">}</a>
    <a id="12421" class="Symbol">→</a> <a id="12423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12410" class="Bound">n</a> <a id="12425" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="12427" href="plfa.part1.Relations.html#12408" class="Bound">m</a>
      <a id="12435" class="Comment">----------</a>
    <a id="12450" class="Symbol">→</a> <a id="12452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12292" class="Datatype">Total′</a> <a id="12459" href="plfa.part1.Relations.html#12408" class="Bound">m</a> <a id="12461" href="plfa.part1.Relations.html#12410" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="12980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12980" class="Function">≤-total</a> <a id="12988" class="Symbol">:</a> <a id="12990" class="Symbol">∀</a> <a id="12992" class="Symbol">(</a><a id="12993" href="plfa.part1.Relations.html#12993" class="Bound">m</a> <a id="12995" href="plfa.part1.Relations.html#12995" class="Bound">n</a> <a id="12997" class="Symbol">:</a> <a id="12999" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13000" class="Symbol">)</a> <a id="13002" class="Symbol">→</a> <a id="13004" href="plfa.part1.Relations.html#11658" class="Datatype">Total</a> <a id="13010" href="plfa.part1.Relations.html#12993" class="Bound">m</a> <a id="13012" href="plfa.part1.Relations.html#12995" class="Bound">n</a>
<a id="13014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12980" class="Function">≤-total</a> <a id="13022" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13030" href="plfa.part1.Relations.html#13030" class="Bound">n</a>                         <a id="13056" class="Symbol">=</a>  <a id="13059" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="13067" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="13071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12980" class="Function">≤-total</a> <a id="13079" class="Symbol">(</a><a id="13080" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13084" href="plfa.part1.Relations.html#13084" class="Bound">m</a><a id="13085" class="Symbol">)</a> <a id="13087" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="13113" class="Symbol">=</a>  <a id="13116" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="13124" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="13128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12980" class="Function">≤-total</a> <a id="13136" class="Symbol">(</a><a id="13137" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13141" href="plfa.part1.Relations.html#13141" class="Bound">m</a><a id="13142" class="Symbol">)</a> <a id="13144" class="Symbol">(</a><a id="13145" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13149" href="plfa.part1.Relations.html#13149" class="Bound">n</a><a id="13150" class="Symbol">)</a> <a id="13152" class="Keyword">with</a> <a id="13157" href="plfa.part1.Relations.html#12980" class="Function">≤-total</a> <a id="13165" href="plfa.part1.Relations.html#13141" class="Bound">m</a> <a id="13167" href="plfa.part1.Relations.html#13149" class="Bound">n</a>
<a id="13169" class="Symbol">...</a>                        <a id="13196" class="Symbol">|</a> <a id="13198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11689" class="InductiveConstructor">forward</a> <a id="13206" href="plfa.part1.Relations.html#13206" class="Bound">m≤n</a>  <a id="13211" class="Symbol">=</a>  <a id="13214" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="13222" class="Symbol">(</a><a id="13223" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="13227" href="plfa.part1.Relations.html#13206" class="Bound">m≤n</a><a id="13230" class="Symbol">)</a>
<a id="13232" class="Symbol">...</a>                        <a id="13259" class="Symbol">|</a> <a id="13261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11746" class="InductiveConstructor">flipped</a> <a id="13269" href="plfa.part1.Relations.html#13269" class="Bound">n≤m</a>  <a id="13274" class="Symbol">=</a>  <a id="13277" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="13285" class="Symbol">(</a><a id="13286" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="13290" href="plfa.part1.Relations.html#13269" class="Bound">n≤m</a><a id="13293" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="14785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14785" class="Function">≤-total′</a> <a id="14794" class="Symbol">:</a> <a id="14796" class="Symbol">∀</a> <a id="14798" class="Symbol">(</a><a id="14799" href="plfa.part1.Relations.html#14799" class="Bound">m</a> <a id="14801" href="plfa.part1.Relations.html#14801" class="Bound">n</a> <a id="14803" class="Symbol">:</a> <a id="14805" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14806" class="Symbol">)</a> <a id="14808" class="Symbol">→</a> <a id="14810" href="plfa.part1.Relations.html#11658" class="Datatype">Total</a> <a id="14816" href="plfa.part1.Relations.html#14799" class="Bound">m</a> <a id="14818" href="plfa.part1.Relations.html#14801" class="Bound">n</a>
<a id="14820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14785" class="Function">≤-total′</a> <a id="14829" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="14837" href="plfa.part1.Relations.html#14837" class="Bound">n</a>        <a id="14846" class="Symbol">=</a>  <a id="14849" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="14857" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="14861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14785" class="Function">≤-total′</a> <a id="14870" class="Symbol">(</a><a id="14871" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14875" href="plfa.part1.Relations.html#14875" class="Bound">m</a><a id="14876" class="Symbol">)</a> <a id="14878" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="14887" class="Symbol">=</a>  <a id="14890" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="14898" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="14902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14785" class="Function">≤-total′</a> <a id="14911" class="Symbol">(</a><a id="14912" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14916" href="plfa.part1.Relations.html#14916" class="Bound">m</a><a id="14917" class="Symbol">)</a> <a id="14919" class="Symbol">(</a><a id="14920" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14924" href="plfa.part1.Relations.html#14924" class="Bound">n</a><a id="14925" class="Symbol">)</a>  <a id="14928" class="Symbol">=</a>  <a id="14931" href="plfa.part1.Relations.html#14963" class="Function">helper</a> <a id="14938" class="Symbol">(</a><a id="14939" href="plfa.part1.Relations.html#14785" class="Function">≤-total′</a> <a id="14948" href="plfa.part1.Relations.html#14916" class="Bound">m</a> <a id="14950" href="plfa.part1.Relations.html#14924" class="Bound">n</a><a id="14951" class="Symbol">)</a>
  <a id="14955" class="Keyword">where</a>
  <a id="14963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14963" class="Function">helper</a> <a id="14970" class="Symbol">:</a> <a id="14972" href="plfa.part1.Relations.html#11658" class="Datatype">Total</a> <a id="14978" href="plfa.part1.Relations.html#14916" class="Bound">m</a> <a id="14980" href="plfa.part1.Relations.html#14924" class="Bound">n</a> <a id="14982" class="Symbol">→</a> <a id="14984" href="plfa.part1.Relations.html#11658" class="Datatype">Total</a> <a id="14990" class="Symbol">(</a><a id="14991" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14995" href="plfa.part1.Relations.html#14916" class="Bound">m</a><a id="14996" class="Symbol">)</a> <a id="14998" class="Symbol">(</a><a id="14999" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15003" href="plfa.part1.Relations.html#14924" class="Bound">n</a><a id="15004" class="Symbol">)</a>
  <a id="15008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14963" class="Function">helper</a> <a id="15015" class="Symbol">(</a><a id="15016" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="15024" href="plfa.part1.Relations.html#15024" class="Bound">m≤n</a><a id="15027" class="Symbol">)</a>  <a id="15030" class="Symbol">=</a>  <a id="15033" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="15041" class="Symbol">(</a><a id="15042" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15046" href="plfa.part1.Relations.html#15024" class="Bound">m≤n</a><a id="15049" class="Symbol">)</a>
  <a id="15053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#14963" class="Function">helper</a> <a id="15060" class="Symbol">(</a><a id="15061" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="15069" href="plfa.part1.Relations.html#15069" class="Bound">n≤m</a><a id="15072" class="Symbol">)</a>  <a id="15075" class="Symbol">=</a>  <a id="15078" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="15086" class="Symbol">(</a><a id="15087" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15091" href="plfa.part1.Relations.html#15069" class="Bound">n≤m</a><a id="15094" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="15716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15716" class="Function">≤-total″</a> <a id="15725" class="Symbol">:</a> <a id="15727" class="Symbol">∀</a> <a id="15729" class="Symbol">(</a><a id="15730" href="plfa.part1.Relations.html#15730" class="Bound">m</a> <a id="15732" href="plfa.part1.Relations.html#15732" class="Bound">n</a> <a id="15734" class="Symbol">:</a> <a id="15736" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15737" class="Symbol">)</a> <a id="15739" class="Symbol">→</a> <a id="15741" href="plfa.part1.Relations.html#11658" class="Datatype">Total</a> <a id="15747" href="plfa.part1.Relations.html#15730" class="Bound">m</a> <a id="15749" href="plfa.part1.Relations.html#15732" class="Bound">n</a>
<a id="15751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15716" class="Function">≤-total″</a> <a id="15760" href="plfa.part1.Relations.html#15760" class="Bound">m</a>       <a id="15768" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="15794" class="Symbol">=</a>  <a id="15797" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="15805" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="15809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15716" class="Function">≤-total″</a> <a id="15818" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15826" class="Symbol">(</a><a id="15827" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15831" href="plfa.part1.Relations.html#15831" class="Bound">n</a><a id="15832" class="Symbol">)</a>                   <a id="15852" class="Symbol">=</a>  <a id="15855" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="15863" href="plfa.part1.Relations.html#1222" class="InductiveConstructor">z≤n</a>
<a id="15867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15716" class="Function">≤-total″</a> <a id="15876" class="Symbol">(</a><a id="15877" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15881" href="plfa.part1.Relations.html#15881" class="Bound">m</a><a id="15882" class="Symbol">)</a> <a id="15884" class="Symbol">(</a><a id="15885" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15889" href="plfa.part1.Relations.html#15889" class="Bound">n</a><a id="15890" class="Symbol">)</a> <a id="15892" class="Keyword">with</a> <a id="15897" href="plfa.part1.Relations.html#15716" class="Function">≤-total″</a> <a id="15906" href="plfa.part1.Relations.html#15881" class="Bound">m</a> <a id="15908" href="plfa.part1.Relations.html#15889" class="Bound">n</a>
<a id="15910" class="Symbol">...</a>                        <a id="15937" class="Symbol">|</a> <a id="15939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11689" class="InductiveConstructor">forward</a> <a id="15947" href="plfa.part1.Relations.html#15947" class="Bound">m≤n</a>   <a id="15953" class="Symbol">=</a>  <a id="15956" href="plfa.part1.Relations.html#11689" class="InductiveConstructor">forward</a> <a id="15964" class="Symbol">(</a><a id="15965" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="15969" href="plfa.part1.Relations.html#15947" class="Bound">m≤n</a><a id="15972" class="Symbol">)</a>
<a id="15974" class="Symbol">...</a>                        <a id="16001" class="Symbol">|</a> <a id="16003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11746" class="InductiveConstructor">flipped</a> <a id="16011" href="plfa.part1.Relations.html#16011" class="Bound">n≤m</a>   <a id="16017" class="Symbol">=</a>  <a id="16020" href="plfa.part1.Relations.html#11746" class="InductiveConstructor">flipped</a> <a id="16028" class="Symbol">(</a><a id="16029" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="16033" href="plfa.part1.Relations.html#16011" class="Bound">n≤m</a><a id="16036" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="16625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16625" class="Function">+-monoʳ-≤</a> <a id="16635" class="Symbol">:</a> <a id="16637" class="Symbol">∀</a> <a id="16639" class="Symbol">(</a><a id="16640" href="plfa.part1.Relations.html#16640" class="Bound">n</a> <a id="16642" href="plfa.part1.Relations.html#16642" class="Bound">p</a> <a id="16644" href="plfa.part1.Relations.html#16644" class="Bound">q</a> <a id="16646" class="Symbol">:</a> <a id="16648" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16649" class="Symbol">)</a>
  <a id="16653" class="Symbol">→</a> <a id="16655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16642" class="Bound">p</a> <a id="16657" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="16659" href="plfa.part1.Relations.html#16644" class="Bound">q</a>
    <a id="16665" class="Comment">-------------</a>
  <a id="16681" class="Symbol">→</a> <a id="16683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16640" class="Bound">n</a> <a id="16685" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16687" href="plfa.part1.Relations.html#16642" class="Bound">p</a> <a id="16689" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="16691" href="plfa.part1.Relations.html#16640" class="Bound">n</a> <a id="16693" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16695" href="plfa.part1.Relations.html#16644" class="Bound">q</a>
<a id="16697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16625" class="Function">+-monoʳ-≤</a> <a id="16707" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16715" href="plfa.part1.Relations.html#16715" class="Bound">p</a> <a id="16717" href="plfa.part1.Relations.html#16717" class="Bound">q</a> <a id="16719" href="plfa.part1.Relations.html#16719" class="Bound">p≤q</a>  <a id="16724" class="Symbol">=</a>  <a id="16727" href="plfa.part1.Relations.html#16719" class="Bound">p≤q</a>
<a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16625" class="Function">+-monoʳ-≤</a> <a id="16741" class="Symbol">(</a><a id="16742" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16746" href="plfa.part1.Relations.html#16746" class="Bound">n</a><a id="16747" class="Symbol">)</a> <a id="16749" href="plfa.part1.Relations.html#16749" class="Bound">p</a> <a id="16751" href="plfa.part1.Relations.html#16751" class="Bound">q</a> <a id="16753" href="plfa.part1.Relations.html#16753" class="Bound">p≤q</a>  <a id="16758" class="Symbol">=</a>  <a id="16761" href="plfa.part1.Relations.html#1271" class="InductiveConstructor">s≤s</a> <a id="16765" class="Symbol">(</a><a id="16766" href="plfa.part1.Relations.html#16625" class="Function">+-monoʳ-≤</a> <a id="16776" href="plfa.part1.Relations.html#16746" class="Bound">n</a> <a id="16778" href="plfa.part1.Relations.html#16749" class="Bound">p</a> <a id="16780" href="plfa.part1.Relations.html#16751" class="Bound">q</a> <a id="16782" href="plfa.part1.Relations.html#16753" class="Bound">p≤q</a><a id="16785" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17425" class="Function">+-monoˡ-≤</a> <a id="17435" class="Symbol">:</a> <a id="17437" class="Symbol">∀</a> <a id="17439" class="Symbol">(</a><a id="17440" href="plfa.part1.Relations.html#17440" class="Bound">m</a> <a id="17442" href="plfa.part1.Relations.html#17442" class="Bound">n</a> <a id="17444" href="plfa.part1.Relations.html#17444" class="Bound">p</a> <a id="17446" class="Symbol">:</a> <a id="17448" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17449" class="Symbol">)</a>
  <a id="17453" class="Symbol">→</a> <a id="17455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17440" class="Bound">m</a> <a id="17457" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17459" href="plfa.part1.Relations.html#17442" class="Bound">n</a>
    <a id="17465" class="Comment">-------------</a>
  <a id="17481" class="Symbol">→</a> <a id="17483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17440" class="Bound">m</a> <a id="17485" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17487" href="plfa.part1.Relations.html#17444" class="Bound">p</a> <a id="17489" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17491" href="plfa.part1.Relations.html#17442" class="Bound">n</a> <a id="17493" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17495" href="plfa.part1.Relations.html#17444" class="Bound">p</a>
<a id="17497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17425" class="Function">+-monoˡ-≤</a> <a id="17507" href="plfa.part1.Relations.html#17507" class="Bound">m</a> <a id="17509" href="plfa.part1.Relations.html#17509" class="Bound">n</a> <a id="17511" href="plfa.part1.Relations.html#17511" class="Bound">p</a> <a id="17513" href="plfa.part1.Relations.html#17513" class="Bound">m≤n</a>  <a id="17518" class="Keyword">rewrite</a> <a id="17526" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17533" href="plfa.part1.Relations.html#17507" class="Bound">m</a> <a id="17535" href="plfa.part1.Relations.html#17511" class="Bound">p</a> <a id="17537" class="Symbol">|</a> <a id="17539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17546" href="plfa.part1.Relations.html#17509" class="Bound">n</a> <a id="17548" href="plfa.part1.Relations.html#17511" class="Bound">p</a>  <a id="17551" class="Symbol">=</a> <a id="17553" href="plfa.part1.Relations.html#16625" class="Function">+-monoʳ-≤</a> <a id="17563" href="plfa.part1.Relations.html#17511" class="Bound">p</a> <a id="17565" href="plfa.part1.Relations.html#17507" class="Bound">m</a> <a id="17567" href="plfa.part1.Relations.html#17509" class="Bound">n</a> <a id="17569" href="plfa.part1.Relations.html#17513" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="17767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17767" class="Function">+-mono-≤</a> <a id="17776" class="Symbol">:</a> <a id="17778" class="Symbol">∀</a> <a id="17780" class="Symbol">(</a><a id="17781" href="plfa.part1.Relations.html#17781" class="Bound">m</a> <a id="17783" href="plfa.part1.Relations.html#17783" class="Bound">n</a> <a id="17785" href="plfa.part1.Relations.html#17785" class="Bound">p</a> <a id="17787" href="plfa.part1.Relations.html#17787" class="Bound">q</a> <a id="17789" class="Symbol">:</a> <a id="17791" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17792" class="Symbol">)</a>
  <a id="17796" class="Symbol">→</a> <a id="17798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17781" class="Bound">m</a> <a id="17800" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17802" href="plfa.part1.Relations.html#17783" class="Bound">n</a>
  <a id="17806" class="Symbol">→</a> <a id="17808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17785" class="Bound">p</a> <a id="17810" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17812" href="plfa.part1.Relations.html#17787" class="Bound">q</a>
    <a id="17818" class="Comment">-------------</a>
  <a id="17834" class="Symbol">→</a> <a id="17836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17781" class="Bound">m</a> <a id="17838" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17840" href="plfa.part1.Relations.html#17785" class="Bound">p</a> <a id="17842" href="plfa.part1.Relations.html#1195" class="Datatype Operator">≤</a> <a id="17844" href="plfa.part1.Relations.html#17783" class="Bound">n</a> <a id="17846" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17848" href="plfa.part1.Relations.html#17787" class="Bound">q</a>
<a id="17850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17767" class="Function">+-mono-≤</a> <a id="17859" href="plfa.part1.Relations.html#17859" class="Bound">m</a> <a id="17861" href="plfa.part1.Relations.html#17861" class="Bound">n</a> <a id="17863" href="plfa.part1.Relations.html#17863" class="Bound">p</a> <a id="17865" href="plfa.part1.Relations.html#17865" class="Bound">q</a> <a id="17867" href="plfa.part1.Relations.html#17867" class="Bound">m≤n</a> <a id="17871" href="plfa.part1.Relations.html#17871" class="Bound">p≤q</a>  <a id="17876" class="Symbol">=</a>  <a id="17879" href="plfa.part1.Relations.html#8361" class="Function">≤-trans</a> <a id="17887" class="Symbol">(</a><a id="17888" href="plfa.part1.Relations.html#17425" class="Function">+-monoˡ-≤</a> <a id="17898" href="plfa.part1.Relations.html#17859" class="Bound">m</a> <a id="17900" href="plfa.part1.Relations.html#17861" class="Bound">n</a> <a id="17902" href="plfa.part1.Relations.html#17863" class="Bound">p</a> <a id="17904" href="plfa.part1.Relations.html#17867" class="Bound">m≤n</a><a id="17907" class="Symbol">)</a> <a id="17909" class="Symbol">(</a><a id="17910" href="plfa.part1.Relations.html#16625" class="Function">+-monoʳ-≤</a> <a id="17920" href="plfa.part1.Relations.html#17861" class="Bound">n</a> <a id="17922" href="plfa.part1.Relations.html#17863" class="Bound">p</a> <a id="17924" href="plfa.part1.Relations.html#17865" class="Bound">q</a> <a id="17926" href="plfa.part1.Relations.html#17871" class="Bound">p≤q</a><a id="17929" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="18238" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18371" class="Keyword">infix</a> <a id="18377" class="Number">4</a> <a id="18379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18389" class="Datatype Operator">_&lt;_</a>

<a id="18384" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18389" class="Datatype Operator">_&lt;_</a> <a id="18393" class="Symbol">:</a> <a id="18395" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18397" class="Symbol">→</a> <a id="18399" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18401" class="Symbol">→</a> <a id="18403" class="PrimitiveType">Set</a> <a id="18407" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18416" class="InductiveConstructor">z&lt;s</a> <a id="18420" class="Symbol">:</a> <a id="18422" class="Symbol">∀</a> <a id="18424" class="Symbol">{</a><a id="18425" href="plfa.part1.Relations.html#18425" class="Bound">n</a> <a id="18427" class="Symbol">:</a> <a id="18429" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18430" class="Symbol">}</a>
      <a id="18438" class="Comment">------------</a>
    <a id="18455" class="Symbol">→</a> <a id="18457" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18389" class="Datatype Operator">&lt;</a> <a id="18464" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18468" href="plfa.part1.Relations.html#18425" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18473" class="InductiveConstructor">s&lt;s</a> <a id="18477" class="Symbol">:</a> <a id="18479" class="Symbol">∀</a> <a id="18481" class="Symbol">{</a><a id="18482" href="plfa.part1.Relations.html#18482" class="Bound">m</a> <a id="18484" href="plfa.part1.Relations.html#18484" class="Bound">n</a> <a id="18486" class="Symbol">:</a> <a id="18488" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18489" class="Symbol">}</a>
    <a id="18495" class="Symbol">→</a> <a id="18497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18482" class="Bound">m</a> <a id="18499" href="plfa.part1.Relations.html#18389" class="Datatype Operator">&lt;</a> <a id="18501" href="plfa.part1.Relations.html#18484" class="Bound">n</a>
      <a id="18509" class="Comment">-------------</a>
    <a id="18527" class="Symbol">→</a> <a id="18529" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18482" class="Bound">m</a> <a id="18535" href="plfa.part1.Relations.html#18389" class="Datatype Operator">&lt;</a> <a id="18537" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18541" href="plfa.part1.Relations.html#18484" class="Bound">n</a>
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

{% raw %}<pre class="Agda"><a id="19710" class="Comment">-- Your code goes here</a>
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

{% raw %}<pre class="Agda"><a id="20209" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20429" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="20572" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="20843" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="21082" class="Keyword">data</a> <a id="even"></a><a id="21087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="21092" class="Symbol">:</a> <a id="21094" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21096" class="Symbol">→</a> <a id="21098" class="PrimitiveType">Set</a>
<a id="21102" class="Keyword">data</a> <a id="odd"></a><a id="21107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a>  <a id="21112" class="Symbol">:</a> <a id="21114" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21116" class="Symbol">→</a> <a id="21118" class="PrimitiveType">Set</a>

<a id="21123" class="Keyword">data</a> <a id="21128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="21133" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21142" class="InductiveConstructor">zero</a> <a id="21147" class="Symbol">:</a>
      <a id="21155" class="Comment">---------</a>
      <a id="21171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="21176" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21184" class="InductiveConstructor">suc</a>  <a id="21189" class="Symbol">:</a> <a id="21191" class="Symbol">∀</a> <a id="21193" class="Symbol">{</a><a id="21194" href="plfa.part1.Relations.html#21194" class="Bound">n</a> <a id="21196" class="Symbol">:</a> <a id="21198" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21199" class="Symbol">}</a>
    <a id="21205" class="Symbol">→</a> <a id="21207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a> <a id="21211" href="plfa.part1.Relations.html#21194" class="Bound">n</a>
      <a id="21219" class="Comment">------------</a>
    <a id="21236" class="Symbol">→</a> <a id="21238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="21243" class="Symbol">(</a><a id="21244" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21248" href="plfa.part1.Relations.html#21194" class="Bound">n</a><a id="21249" class="Symbol">)</a>

<a id="21252" class="Keyword">data</a> <a id="21257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a> <a id="21261" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21270" class="InductiveConstructor">suc</a>   <a id="21276" class="Symbol">:</a> <a id="21278" class="Symbol">∀</a> <a id="21280" class="Symbol">{</a><a id="21281" href="plfa.part1.Relations.html#21281" class="Bound">n</a> <a id="21283" class="Symbol">:</a> <a id="21285" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21286" class="Symbol">}</a>
    <a id="21292" class="Symbol">→</a> <a id="21294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="21299" href="plfa.part1.Relations.html#21281" class="Bound">n</a>
      <a id="21307" class="Comment">-----------</a>
    <a id="21323" class="Symbol">→</a> <a id="21325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a> <a id="21329" class="Symbol">(</a><a id="21330" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21334" href="plfa.part1.Relations.html#21281" class="Bound">n</a><a id="21335" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="22495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22495" class="Function">e+e≡e</a> <a id="22501" class="Symbol">:</a> <a id="22503" class="Symbol">∀</a> <a id="22505" class="Symbol">{</a><a id="22506" href="plfa.part1.Relations.html#22506" class="Bound">m</a> <a id="22508" href="plfa.part1.Relations.html#22508" class="Bound">n</a> <a id="22510" class="Symbol">:</a> <a id="22512" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22513" class="Symbol">}</a>
  <a id="22517" class="Symbol">→</a> <a id="22519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="22524" href="plfa.part1.Relations.html#22506" class="Bound">m</a>
  <a id="22528" class="Symbol">→</a> <a id="22530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="22535" href="plfa.part1.Relations.html#22508" class="Bound">n</a>
    <a id="22541" class="Comment">------------</a>
  <a id="22556" class="Symbol">→</a> <a id="22558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="22563" class="Symbol">(</a><a id="22564" href="plfa.part1.Relations.html#22506" class="Bound">m</a> <a id="22566" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22568" href="plfa.part1.Relations.html#22508" class="Bound">n</a><a id="22569" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22572" class="Function">o+e≡o</a> <a id="22578" class="Symbol">:</a> <a id="22580" class="Symbol">∀</a> <a id="22582" class="Symbol">{</a><a id="22583" href="plfa.part1.Relations.html#22583" class="Bound">m</a> <a id="22585" href="plfa.part1.Relations.html#22585" class="Bound">n</a> <a id="22587" class="Symbol">:</a> <a id="22589" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22590" class="Symbol">}</a>
  <a id="22594" class="Symbol">→</a> <a id="22596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a> <a id="22600" href="plfa.part1.Relations.html#22583" class="Bound">m</a>
  <a id="22604" class="Symbol">→</a> <a id="22606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21087" class="Datatype">even</a> <a id="22611" href="plfa.part1.Relations.html#22585" class="Bound">n</a>
    <a id="22617" class="Comment">-----------</a>
  <a id="22631" class="Symbol">→</a> <a id="22633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21107" class="Datatype">odd</a> <a id="22637" class="Symbol">(</a><a id="22638" href="plfa.part1.Relations.html#22583" class="Bound">m</a> <a id="22640" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22642" href="plfa.part1.Relations.html#22585" class="Bound">n</a><a id="22643" class="Symbol">)</a>

<a id="22646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22495" class="Function">e+e≡e</a> <a id="22652" href="plfa.part1.Relations.html#21142" class="InductiveConstructor">zero</a>     <a id="22661" href="plfa.part1.Relations.html#22661" class="Bound">en</a>  <a id="22665" class="Symbol">=</a>  <a id="22668" href="plfa.part1.Relations.html#22661" class="Bound">en</a>
<a id="22671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22495" class="Function">e+e≡e</a> <a id="22677" class="Symbol">(</a><a id="22678" href="plfa.part1.Relations.html#21184" class="InductiveConstructor">suc</a> <a id="22682" href="plfa.part1.Relations.html#22682" class="Bound">om</a><a id="22684" class="Symbol">)</a> <a id="22686" href="plfa.part1.Relations.html#22686" class="Bound">en</a>  <a id="22690" class="Symbol">=</a>  <a id="22693" href="plfa.part1.Relations.html#21184" class="InductiveConstructor">suc</a> <a id="22697" class="Symbol">(</a><a id="22698" href="plfa.part1.Relations.html#22572" class="Function">o+e≡o</a> <a id="22704" href="plfa.part1.Relations.html#22682" class="Bound">om</a> <a id="22707" href="plfa.part1.Relations.html#22686" class="Bound">en</a><a id="22709" class="Symbol">)</a>

<a id="22712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#22572" class="Function">o+e≡o</a> <a id="22718" class="Symbol">(</a><a id="22719" href="plfa.part1.Relations.html#21270" class="InductiveConstructor">suc</a> <a id="22723" href="plfa.part1.Relations.html#22723" class="Bound">em</a><a id="22725" class="Symbol">)</a> <a id="22727" href="plfa.part1.Relations.html#22727" class="Bound">en</a>  <a id="22731" class="Symbol">=</a>  <a id="22734" href="plfa.part1.Relations.html#21270" class="InductiveConstructor">suc</a> <a id="22738" class="Symbol">(</a><a id="22739" href="plfa.part1.Relations.html#22495" class="Function">e+e≡e</a> <a id="22745" href="plfa.part1.Relations.html#22723" class="Bound">em</a> <a id="22748" href="plfa.part1.Relations.html#22727" class="Bound">en</a><a id="22750" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="23888" class="Comment">-- Your code goes here</a>
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

    Can x
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
properties of `One`.)

{% raw %}<pre class="Agda"><a id="25168" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25304" class="Keyword">import</a> <a id="25311" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25320" class="Keyword">using</a> <a id="25326" class="Symbol">(</a><a id="25327" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25330" class="Symbol">;</a> <a id="25332" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25335" class="Symbol">;</a> <a id="25337" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25340" class="Symbol">)</a>
<a id="25342" class="Keyword">import</a> <a id="25349" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25369" class="Keyword">using</a> <a id="25375" class="Symbol">(</a><a id="25376" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25382" class="Symbol">;</a> <a id="25384" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="25391" class="Symbol">;</a> <a id="25393" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="25402" class="Symbol">;</a> <a id="25404" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="25411" class="Symbol">;</a>
                                  <a id="25447" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="25456" class="Symbol">;</a> <a id="25458" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="25467" class="Symbol">;</a> <a id="25469" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="25477" class="Symbol">)</a>
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
