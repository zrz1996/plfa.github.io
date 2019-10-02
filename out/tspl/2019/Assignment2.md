---
src       : "courses/tspl/2019/Assignment2.lagda.md"
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /TSPL/2019/Assignment2/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}" class="Module">Assignment2</a> <a id="131" class="Keyword">where</a>
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

{% raw %}<pre class="Agda"><a id="1198" class="Keyword">import</a> <a id="1205" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1243" class="Symbol">as</a> <a id="1246" class="Module">Eq</a>
<a id="1249" class="Keyword">open</a> <a id="1254" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1257" class="Keyword">using</a> <a id="1263" class="Symbol">(</a><a id="1264" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1267" class="Symbol">;</a> <a id="1269" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1273" class="Symbol">;</a> <a id="1275" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1279" class="Symbol">;</a> <a id="1281" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1284" class="Symbol">)</a>
<a id="1286" class="Keyword">open</a> <a id="1291" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1306" class="Keyword">using</a> <a id="1312" class="Symbol">(</a><a id="1313" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1319" class="Symbol">;</a> <a id="1321" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1326" class="Symbol">;</a> <a id="1328" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1334" class="Symbol">;</a> <a id="1336" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1338" class="Symbol">)</a>
<a id="1340" class="Keyword">open</a> <a id="1345" class="Keyword">import</a> <a id="1352" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1361" class="Keyword">using</a> <a id="1367" class="Symbol">(</a><a id="1368" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1369" class="Symbol">;</a> <a id="1371" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1375" class="Symbol">;</a> <a id="1377" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1380" class="Symbol">;</a> <a id="1382" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1385" class="Symbol">;</a> <a id="1387" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1390" class="Symbol">;</a> <a id="1392" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1395" class="Symbol">;</a> <a id="1397" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="1400" class="Symbol">;</a> <a id="1402" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="1405" class="Symbol">;</a> <a id="1407" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="1410" class="Symbol">)</a>
<a id="1412" class="Keyword">open</a> <a id="1417" class="Keyword">import</a> <a id="1424" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="1444" class="Keyword">using</a> <a id="1450" class="Symbol">(</a><a id="1451" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="1458" class="Symbol">;</a> <a id="1460" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="1471" class="Symbol">;</a> <a id="1473" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="1478" class="Symbol">;</a> <a id="1480" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="1486" class="Symbol">;</a>
  <a id="1490" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="1496" class="Symbol">;</a> <a id="1498" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="1505" class="Symbol">;</a> <a id="1507" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1516" class="Symbol">;</a> <a id="1518" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1525" class="Symbol">;</a> <a id="1527" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1536" class="Symbol">;</a> <a id="1538" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1547" class="Symbol">;</a> <a id="1549" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1557" class="Symbol">)</a>
<a id="1559" class="Keyword">open</a> <a id="1564" class="Keyword">import</a> <a id="1571" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1584" class="Keyword">using</a> <a id="1590" class="Symbol">(</a><a id="1591" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1594" class="Symbol">;</a> <a id="1596" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1601" class="Symbol">;</a> <a id="1603" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1608" class="Symbol">)</a> <a id="1610" class="Keyword">renaming</a> <a id="1619" class="Symbol">(</a><a id="1620" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1624" class="Symbol">to</a> <a id="1627" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1632" class="Symbol">)</a>
<a id="1634" class="Keyword">open</a> <a id="1639" class="Keyword">import</a> <a id="1646" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1656" class="Keyword">using</a> <a id="1662" class="Symbol">(</a><a id="1663" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1664" class="Symbol">;</a> <a id="1666" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1668" class="Symbol">)</a>
<a id="1670" class="Keyword">open</a> <a id="1675" class="Keyword">import</a> <a id="1682" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1691" class="Keyword">using</a> <a id="1697" class="Symbol">(</a><a id="1698" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1701" class="Symbol">;</a> <a id="1703" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1707" class="Symbol">;</a> <a id="1709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1713" class="Symbol">)</a> <a id="1715" class="Keyword">renaming</a> <a id="1724" class="Symbol">(</a><a id="1725" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1731" class="Symbol">to</a> <a id="1734" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1740" class="Symbol">)</a>
<a id="1742" class="Keyword">open</a> <a id="1747" class="Keyword">import</a> <a id="1754" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1765" class="Keyword">using</a> <a id="1771" class="Symbol">(</a><a id="1772" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1773" class="Symbol">;</a> <a id="1775" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1781" class="Symbol">)</a>
<a id="1783" class="Keyword">open</a> <a id="1788" class="Keyword">import</a> <a id="1795" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1810" class="Keyword">using</a> <a id="1816" class="Symbol">(</a><a id="1817" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1821" class="Symbol">;</a> <a id="1823" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1827" class="Symbol">;</a> <a id="1829" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1834" class="Symbol">;</a> <a id="1836" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1837" class="Symbol">;</a> <a id="1839" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1842" class="Symbol">;</a> <a id="1844" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1847" class="Symbol">;</a> <a id="1849" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1852" class="Symbol">)</a>
<a id="1854" class="Keyword">open</a> <a id="1859" class="Keyword">import</a> <a id="1866" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1883" class="Keyword">using</a> <a id="1889" class="Symbol">(</a><a id="1890" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1892" class="Symbol">;</a> <a id="1894" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1897" class="Symbol">;</a> <a id="1899" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1902" class="Symbol">;</a> <a id="1904" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1906" class="Symbol">)</a>
<a id="1908" class="Keyword">open</a> <a id="1913" class="Keyword">import</a> <a id="1920" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1947" class="Keyword">using</a> <a id="1953" class="Symbol">(</a><a id="1954" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1957" class="Symbol">;</a> <a id="1959" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1968" class="Symbol">;</a> <a id="1970" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1981" class="Symbol">)</a>
<a id="1983" class="Keyword">open</a> <a id="1988" class="Keyword">import</a> <a id="1995" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="2021" class="Keyword">using</a> <a id="2027" class="Symbol">(</a><a id="2028" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="2030" class="Symbol">)</a>
<a id="2032" class="Keyword">open</a> <a id="2037" class="Keyword">import</a> <a id="2044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="2069" class="Keyword">using</a> <a id="2075" class="Symbol">(</a><a id="2076" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="2083" class="Symbol">)</a>
<a id="2085" class="Keyword">open</a> <a id="2090" class="Keyword">import</a> <a id="2097" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="2118" class="Keyword">using</a> <a id="2124" class="Symbol">(</a><a id="2125" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="2132" class="Symbol">)</a>
<a id="2134" class="Keyword">open</a> <a id="2139" class="Keyword">import</a> <a id="2146" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="2172" class="Keyword">using</a> <a id="2178" class="Symbol">(</a><a id="2179" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="2193" class="Symbol">)</a>
<a id="2195" class="Keyword">open</a> <a id="2200" class="Keyword">import</a> <a id="2207" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="2220" class="Keyword">using</a> <a id="2226" class="Symbol">(</a><a id="2227" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="2228" class="Symbol">;</a> <a id="2230" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="2233" class="Symbol">;</a> <a id="2235" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="2236" class="Symbol">;</a> <a id="2238" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="2246" class="Symbol">;</a> <a id="2248" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="2256" class="Symbol">)</a>
<a id="2258" class="Keyword">open</a> <a id="2263" class="Keyword">import</a> <a id="2270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="2291" class="Keyword">using</a> <a id="2297" class="Symbol">(</a><a id="2298" href="plfa.part1.Relations.html#18383" class="Datatype Operator">_&lt;_</a><a id="2301" class="Symbol">;</a> <a id="2303" href="plfa.part1.Relations.html#18410" class="InductiveConstructor">z&lt;s</a><a id="2306" class="Symbol">;</a> <a id="2308" href="plfa.part1.Relations.html#18467" class="InductiveConstructor">s&lt;s</a><a id="2311" class="Symbol">)</a>
<a id="2313" class="Keyword">open</a> <a id="2318" class="Keyword">import</a> <a id="2325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="2348" class="Keyword">using</a> <a id="2354" class="Symbol">(</a><a id="2355" href="plfa.part1.Isomorphism.html#4365" class="Record Operator">_≃_</a><a id="2358" class="Symbol">;</a> <a id="2360" href="plfa.part1.Isomorphism.html#7012" class="Function">≃-sym</a><a id="2365" class="Symbol">;</a> <a id="2367" href="plfa.part1.Isomorphism.html#7337" class="Function">≃-trans</a><a id="2374" class="Symbol">;</a> <a id="2376" href="plfa.part1.Isomorphism.html#9186" class="Record Operator">_≲_</a><a id="2379" class="Symbol">;</a> <a id="2381" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a><a id="2395" class="Symbol">)</a>
<a id="2397" class="Keyword">open</a> <a id="2402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#8421" class="Module">plfa.part1.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}
## Equality


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

{% raw %}<pre class="Agda"><a id="3093" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Isomorphism

#### Exercise `≃-implies-≲` (practice)

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="3231" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="3243" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3243" class="Postulate">≃-implies-≲</a> <a id="3255" class="Symbol">:</a> <a id="3257" class="Symbol">∀</a> <a id="3259" class="Symbol">{</a><a id="3260" href="Assignment2.html#3260" class="Bound">A</a> <a id="3262" href="Assignment2.html#3262" class="Bound">B</a> <a id="3264" class="Symbol">:</a> <a id="3266" class="PrimitiveType">Set</a><a id="3269" class="Symbol">}</a>
    <a id="3275" class="Symbol">→</a> <a id="3277" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3260" class="Bound">A</a> <a id="3279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="3281" href="Assignment2.html#3262" class="Bound">B</a>
      <a id="3289" class="Comment">-----</a>
    <a id="3299" class="Symbol">→</a> <a id="3301" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3260" class="Bound">A</a> <a id="3303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#9186" class="Record Operator">≲</a> <a id="3305" href="Assignment2.html#3262" class="Bound">B</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="3316" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (practice) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows:
{% raw %}<pre class="Agda"><a id="3467" class="Keyword">record</a> <a id="_⇔_"></a><a id="3474" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3474" class="Record Operator">_⇔_</a> <a id="3478" class="Symbol">(</a><a id="3479" href="Assignment2.html#3479" class="Bound">A</a> <a id="3481" href="Assignment2.html#3481" class="Bound">B</a> <a id="3483" class="Symbol">:</a> <a id="3485" class="PrimitiveType">Set</a><a id="3488" class="Symbol">)</a> <a id="3490" class="Symbol">:</a> <a id="3492" class="PrimitiveType">Set</a> <a id="3496" class="Keyword">where</a>
  <a id="3504" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="3514" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3514" class="Field">to</a>   <a id="3519" class="Symbol">:</a> <a id="3521" href="Assignment2.html#3479" class="Bound">A</a> <a id="3523" class="Symbol">→</a> <a id="3525" href="Assignment2.html#3481" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="3531" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#3531" class="Field">from</a> <a id="3536" class="Symbol">:</a> <a id="3538" href="Assignment2.html#3481" class="Bound">B</a> <a id="3540" class="Symbol">→</a> <a id="3542" href="Assignment2.html#3479" class="Bound">A</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

{% raw %}<pre class="Agda"><a id="3616" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin) and
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{% raw %}<pre class="Agda"><a id="4125" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Why do `to` and `from` not form an isomorphism?

## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

{% raw %}<pre class="Agda"><a id="4372" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

{% raw %}<pre class="Agda"><a id="4486" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

{% raw %}<pre class="Agda"><a id="4598" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="4733" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="4866" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
{% raw %}<pre class="Agda"><a id="4978" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#4990" class="Postulate">⊎-weak-×</a> <a id="4999" class="Symbol">:</a> <a id="5001" class="Symbol">∀</a> <a id="5003" class="Symbol">{</a><a id="5004" href="Assignment2.html#5004" class="Bound">A</a> <a id="5006" href="Assignment2.html#5006" class="Bound">B</a> <a id="5008" href="Assignment2.html#5008" class="Bound">C</a> <a id="5010" class="Symbol">:</a> <a id="5012" class="PrimitiveType">Set</a><a id="5015" class="Symbol">}</a> <a id="5017" class="Symbol">→</a> <a id="5019" class="Symbol">(</a><a id="5020" href="Assignment2.html#5004" class="Bound">A</a> <a id="5022" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5024" href="Assignment2.html#5006" class="Bound">B</a><a id="5025" class="Symbol">)</a> <a id="5027" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5029" href="Assignment2.html#5008" class="Bound">C</a> <a id="5031" class="Symbol">→</a> <a id="5033" href="Assignment2.html#5004" class="Bound">A</a> <a id="5035" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5037" class="Symbol">(</a><a id="5038" href="Assignment2.html#5006" class="Bound">B</a> <a id="5040" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5042" href="Assignment2.html#5008" class="Bound">C</a><a id="5043" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

{% raw %}<pre class="Agda"><a id="5185" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{% raw %}<pre class="Agda"><a id="5327" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="5339" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#5339" class="Postulate">⊎×-implies-×⊎</a> <a id="5353" class="Symbol">:</a> <a id="5355" class="Symbol">∀</a> <a id="5357" class="Symbol">{</a><a id="5358" href="Assignment2.html#5358" class="Bound">A</a> <a id="5360" href="Assignment2.html#5360" class="Bound">B</a> <a id="5362" href="Assignment2.html#5362" class="Bound">C</a> <a id="5364" href="Assignment2.html#5364" class="Bound">D</a> <a id="5366" class="Symbol">:</a> <a id="5368" class="PrimitiveType">Set</a><a id="5371" class="Symbol">}</a> <a id="5373" class="Symbol">→</a> <a id="5375" class="Symbol">(</a><a id="5376" href="Assignment2.html#5358" class="Bound">A</a> <a id="5378" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5380" href="Assignment2.html#5360" class="Bound">B</a><a id="5381" class="Symbol">)</a> <a id="5383" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5385" class="Symbol">(</a><a id="5386" href="Assignment2.html#5362" class="Bound">C</a> <a id="5388" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5390" href="Assignment2.html#5364" class="Bound">D</a><a id="5391" class="Symbol">)</a> <a id="5393" class="Symbol">→</a> <a id="5395" class="Symbol">(</a><a id="5396" href="Assignment2.html#5358" class="Bound">A</a> <a id="5398" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5400" href="Assignment2.html#5362" class="Bound">C</a><a id="5401" class="Symbol">)</a> <a id="5403" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="5405" class="Symbol">(</a><a id="5406" href="Assignment2.html#5360" class="Bound">B</a> <a id="5408" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5410" href="Assignment2.html#5364" class="Bound">D</a><a id="5411" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="5491" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

{% raw %}<pre class="Agda"><a id="5728" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

{% raw %}<pre class="Agda"><a id="6138" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

{% raw %}<pre class="Agda"><a id="6410" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?

#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

{% raw %}<pre class="Agda"><a id="7025" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="7168" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7168" class="Function">Stable</a> <a id="7175" class="Symbol">:</a> <a id="7177" class="PrimitiveType">Set</a> <a id="7181" class="Symbol">→</a> <a id="7183" class="PrimitiveType">Set</a>
<a id="7187" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7168" class="Function">Stable</a> <a id="7194" href="Assignment2.html#7194" class="Bound">A</a> <a id="7196" class="Symbol">=</a> <a id="7198" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7200" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7202" href="Assignment2.html#7194" class="Bound">A</a> <a id="7204" class="Symbol">→</a> <a id="7206" href="Assignment2.html#7194" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

{% raw %}<pre class="Agda"><a id="7317" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Quantifiers


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
{% raw %}<pre class="Agda"><a id="7459" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="7471" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7471" class="Postulate">∀-distrib-×</a> <a id="7483" class="Symbol">:</a> <a id="7485" class="Symbol">∀</a> <a id="7487" class="Symbol">{</a><a id="7488" href="Assignment2.html#7488" class="Bound">A</a> <a id="7490" class="Symbol">:</a> <a id="7492" class="PrimitiveType">Set</a><a id="7495" class="Symbol">}</a> <a id="7497" class="Symbol">{</a><a id="7498" href="Assignment2.html#7498" class="Bound">B</a> <a id="7500" href="Assignment2.html#7500" class="Bound">C</a> <a id="7502" class="Symbol">:</a> <a id="7504" href="Assignment2.html#7488" class="Bound">A</a> <a id="7506" class="Symbol">→</a> <a id="7508" class="PrimitiveType">Set</a><a id="7511" class="Symbol">}</a> <a id="7513" class="Symbol">→</a>
    <a id="7519" class="Symbol">(∀</a> <a id="7522" class="Symbol">(</a><a id="7523" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7523" class="Bound">x</a> <a id="7525" class="Symbol">:</a> <a id="7527" href="Assignment2.html#7488" class="Bound">A</a><a id="7528" class="Symbol">)</a> <a id="7530" class="Symbol">→</a> <a id="7532" href="Assignment2.html#7498" class="Bound">B</a> <a id="7534" href="Assignment2.html#7523" class="Bound">x</a> <a id="7536" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7538" href="Assignment2.html#7500" class="Bound">C</a> <a id="7540" href="Assignment2.html#7523" class="Bound">x</a><a id="7541" class="Symbol">)</a> <a id="7543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="7545" class="Symbol">(∀</a> <a id="7548" class="Symbol">(</a><a id="7549" href="Assignment2.html#7549" class="Bound">x</a> <a id="7551" class="Symbol">:</a> <a id="7553" href="Assignment2.html#7488" class="Bound">A</a><a id="7554" class="Symbol">)</a> <a id="7556" class="Symbol">→</a> <a id="7558" href="Assignment2.html#7498" class="Bound">B</a> <a id="7560" href="Assignment2.html#7549" class="Bound">x</a><a id="7561" class="Symbol">)</a> <a id="7563" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7565" class="Symbol">(∀</a> <a id="7568" class="Symbol">(</a><a id="7569" href="Assignment2.html#7569" class="Bound">x</a> <a id="7571" class="Symbol">:</a> <a id="7573" href="Assignment2.html#7488" class="Bound">A</a><a id="7574" class="Symbol">)</a> <a id="7576" class="Symbol">→</a> <a id="7578" href="Assignment2.html#7500" class="Bound">C</a> <a id="7580" href="Assignment2.html#7569" class="Bound">x</a><a id="7581" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).


#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="7814" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="7826" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7826" class="Postulate">⊎∀-implies-∀⊎</a> <a id="7840" class="Symbol">:</a> <a id="7842" class="Symbol">∀</a> <a id="7844" class="Symbol">{</a><a id="7845" href="Assignment2.html#7845" class="Bound">A</a> <a id="7847" class="Symbol">:</a> <a id="7849" class="PrimitiveType">Set</a><a id="7852" class="Symbol">}</a> <a id="7854" class="Symbol">{</a><a id="7855" href="Assignment2.html#7855" class="Bound">B</a> <a id="7857" href="Assignment2.html#7857" class="Bound">C</a> <a id="7859" class="Symbol">:</a> <a id="7861" href="Assignment2.html#7845" class="Bound">A</a> <a id="7863" class="Symbol">→</a> <a id="7865" class="PrimitiveType">Set</a><a id="7868" class="Symbol">}</a> <a id="7870" class="Symbol">→</a>
    <a id="7876" class="Symbol">(∀</a> <a id="7879" class="Symbol">(</a><a id="7880" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#7880" class="Bound">x</a> <a id="7882" class="Symbol">:</a> <a id="7884" href="Assignment2.html#7845" class="Bound">A</a><a id="7885" class="Symbol">)</a> <a id="7887" class="Symbol">→</a> <a id="7889" href="Assignment2.html#7855" class="Bound">B</a> <a id="7891" href="Assignment2.html#7880" class="Bound">x</a><a id="7892" class="Symbol">)</a> <a id="7894" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="7896" class="Symbol">(∀</a> <a id="7899" class="Symbol">(</a><a id="7900" href="Assignment2.html#7900" class="Bound">x</a> <a id="7902" class="Symbol">:</a> <a id="7904" href="Assignment2.html#7845" class="Bound">A</a><a id="7905" class="Symbol">)</a> <a id="7907" class="Symbol">→</a> <a id="7909" href="Assignment2.html#7857" class="Bound">C</a> <a id="7911" href="Assignment2.html#7900" class="Bound">x</a><a id="7912" class="Symbol">)</a>  <a id="7915" class="Symbol">→</a>  <a id="7918" class="Symbol">∀</a> <a id="7920" class="Symbol">(</a><a id="7921" href="Assignment2.html#7921" class="Bound">x</a> <a id="7923" class="Symbol">:</a> <a id="7925" href="Assignment2.html#7845" class="Bound">A</a><a id="7926" class="Symbol">)</a> <a id="7928" class="Symbol">→</a> <a id="7930" href="Assignment2.html#7855" class="Bound">B</a> <a id="7932" href="Assignment2.html#7921" class="Bound">x</a> <a id="7934" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="7936" href="Assignment2.html#7857" class="Bound">C</a> <a id="7938" href="Assignment2.html#7921" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
{% raw %}<pre class="Agda"><a id="8070" class="Keyword">data</a> <a id="Tri"></a><a id="8075" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8075" class="Datatype">Tri</a> <a id="8079" class="Symbol">:</a> <a id="8081" class="PrimitiveType">Set</a> <a id="8085" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="8093" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8093" class="InductiveConstructor">aa</a> <a id="8096" class="Symbol">:</a> <a id="8098" href="Assignment2.html#8075" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="8104" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8104" class="InductiveConstructor">bb</a> <a id="8107" class="Symbol">:</a> <a id="8109" href="Assignment2.html#8075" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="8115" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8115" class="InductiveConstructor">cc</a> <a id="8118" class="Symbol">:</a> <a id="8120" href="Assignment2.html#8075" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.


#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8359" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8371" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8371" class="Postulate">∃-distrib-⊎</a> <a id="8383" class="Symbol">:</a> <a id="8385" class="Symbol">∀</a> <a id="8387" class="Symbol">{</a><a id="8388" href="Assignment2.html#8388" class="Bound">A</a> <a id="8390" class="Symbol">:</a> <a id="8392" class="PrimitiveType">Set</a><a id="8395" class="Symbol">}</a> <a id="8397" class="Symbol">{</a><a id="8398" href="Assignment2.html#8398" class="Bound">B</a> <a id="8400" href="Assignment2.html#8400" class="Bound">C</a> <a id="8402" class="Symbol">:</a> <a id="8404" href="Assignment2.html#8388" class="Bound">A</a> <a id="8406" class="Symbol">→</a> <a id="8408" class="PrimitiveType">Set</a><a id="8411" class="Symbol">}</a> <a id="8413" class="Symbol">→</a>
    <a id="8419" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8422" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8422" class="Bound">x</a> <a id="8424" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8426" class="Symbol">(</a><a id="8427" href="Assignment2.html#8398" class="Bound">B</a> <a id="8429" href="Assignment2.html#8422" class="Bound">x</a> <a id="8431" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8433" href="Assignment2.html#8400" class="Bound">C</a> <a id="8435" href="Assignment2.html#8422" class="Bound">x</a><a id="8436" class="Symbol">)</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8440" class="Symbol">(</a><a id="8441" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8444" href="Assignment2.html#8444" class="Bound">x</a> <a id="8446" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8448" href="Assignment2.html#8398" class="Bound">B</a> <a id="8450" href="Assignment2.html#8444" class="Bound">x</a><a id="8451" class="Symbol">)</a> <a id="8453" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8455" class="Symbol">(</a><a id="8456" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8459" href="Assignment2.html#8459" class="Bound">x</a> <a id="8461" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8463" href="Assignment2.html#8400" class="Bound">C</a> <a id="8465" href="Assignment2.html#8459" class="Bound">x</a><a id="8466" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="8600" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="8612" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8612" class="Postulate">∃×-implies-×∃</a> <a id="8626" class="Symbol">:</a> <a id="8628" class="Symbol">∀</a> <a id="8630" class="Symbol">{</a><a id="8631" href="Assignment2.html#8631" class="Bound">A</a> <a id="8633" class="Symbol">:</a> <a id="8635" class="PrimitiveType">Set</a><a id="8638" class="Symbol">}</a> <a id="8640" class="Symbol">{</a><a id="8641" href="Assignment2.html#8641" class="Bound">B</a> <a id="8643" href="Assignment2.html#8643" class="Bound">C</a> <a id="8645" class="Symbol">:</a> <a id="8647" href="Assignment2.html#8631" class="Bound">A</a> <a id="8649" class="Symbol">→</a> <a id="8651" class="PrimitiveType">Set</a><a id="8654" class="Symbol">}</a> <a id="8656" class="Symbol">→</a>
    <a id="8662" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8665" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#8665" class="Bound">x</a> <a id="8667" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8669" class="Symbol">(</a><a id="8670" href="Assignment2.html#8641" class="Bound">B</a> <a id="8672" href="Assignment2.html#8665" class="Bound">x</a> <a id="8674" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8676" href="Assignment2.html#8643" class="Bound">C</a> <a id="8678" href="Assignment2.html#8665" class="Bound">x</a><a id="8679" class="Symbol">)</a> <a id="8681" class="Symbol">→</a> <a id="8683" class="Symbol">(</a><a id="8684" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8687" href="Assignment2.html#8687" class="Bound">x</a> <a id="8689" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8691" href="Assignment2.html#8641" class="Bound">B</a> <a id="8693" href="Assignment2.html#8687" class="Bound">x</a><a id="8694" class="Symbol">)</a> <a id="8696" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8698" class="Symbol">(</a><a id="8699" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="8702" href="Assignment2.html#8702" class="Bound">x</a> <a id="8704" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="8706" href="Assignment2.html#8643" class="Bound">C</a> <a id="8708" href="Assignment2.html#8702" class="Bound">x</a><a id="8709" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

{% raw %}<pre class="Agda"><a id="9136" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-|-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="9284" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
{% raw %}<pre class="Agda"><a id="9431" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="9443" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9443" class="Postulate">∃¬-implies-¬∀</a> <a id="9457" class="Symbol">:</a> <a id="9459" class="Symbol">∀</a> <a id="9461" class="Symbol">{</a><a id="9462" href="Assignment2.html#9462" class="Bound">A</a> <a id="9464" class="Symbol">:</a> <a id="9466" class="PrimitiveType">Set</a><a id="9469" class="Symbol">}</a> <a id="9471" class="Symbol">{</a><a id="9472" href="Assignment2.html#9472" class="Bound">B</a> <a id="9474" class="Symbol">:</a> <a id="9476" href="Assignment2.html#9462" class="Bound">A</a> <a id="9478" class="Symbol">→</a> <a id="9480" class="PrimitiveType">Set</a><a id="9483" class="Symbol">}</a>
    <a id="9489" class="Symbol">→</a> <a id="9491" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="9494" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9494" class="Bound">x</a> <a id="9496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="9498" class="Symbol">(</a><a id="9499" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="9501" href="Assignment2.html#9472" class="Bound">B</a> <a id="9503" href="Assignment2.html#9494" class="Bound">x</a><a id="9504" class="Symbol">)</a>
      <a id="9512" class="Comment">--------------</a>
    <a id="9531" class="Symbol">→</a> <a id="9533" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="9535" class="Symbol">(∀</a> <a id="9538" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#9538" class="Bound">x</a> <a id="9540" class="Symbol">→</a> <a id="9542" href="Assignment2.html#9472" class="Bound">B</a> <a id="9544" href="Assignment2.html#9538" class="Bound">x</a><a id="9545" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

{% raw %}<pre class="Agda"><a id="10289" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Decidable


#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:
{% raw %}<pre class="Agda"><a id="10452" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="10464" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10464" class="Postulate Operator">_&lt;?_</a> <a id="10469" class="Symbol">:</a> <a id="10471" class="Symbol">∀</a> <a id="10473" class="Symbol">(</a><a id="10474" href="Assignment2.html#10474" class="Bound">m</a> <a id="10476" href="Assignment2.html#10476" class="Bound">n</a> <a id="10478" class="Symbol">:</a> <a id="10480" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10481" class="Symbol">)</a> <a id="10483" class="Symbol">→</a> <a id="10485" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10489" class="Symbol">(</a><a id="10490" href="Assignment2.html#10474" class="Bound">m</a> <a id="10492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Datatype Operator">&lt;</a> <a id="10494" href="Assignment2.html#10476" class="Bound">n</a><a id="10495" class="Symbol">)</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="10506" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_` (practice)

Define a function to decide whether two naturals are equal:
{% raw %}<pre class="Agda"><a id="10632" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="10644" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10644" class="Postulate Operator">_≡ℕ?_</a> <a id="10650" class="Symbol">:</a> <a id="10652" class="Symbol">∀</a> <a id="10654" class="Symbol">(</a><a id="10655" href="Assignment2.html#10655" class="Bound">m</a> <a id="10657" href="Assignment2.html#10657" class="Bound">n</a> <a id="10659" class="Symbol">:</a> <a id="10661" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10662" class="Symbol">)</a> <a id="10664" class="Symbol">→</a> <a id="10666" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10670" class="Symbol">(</a><a id="10671" href="Assignment2.html#10655" class="Bound">m</a> <a id="10673" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10675" href="Assignment2.html#10657" class="Bound">n</a><a id="10676" class="Symbol">)</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="10687" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `erasure` (practice)

Show that erasure relates corresponding boolean and decidable operations:
{% raw %}<pre class="Agda"><a id="10830" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="10842" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10842" class="Postulate">∧-×</a> <a id="10846" class="Symbol">:</a> <a id="10848" class="Symbol">∀</a> <a id="10850" class="Symbol">{</a><a id="10851" href="Assignment2.html#10851" class="Bound">A</a> <a id="10853" href="Assignment2.html#10853" class="Bound">B</a> <a id="10855" class="Symbol">:</a> <a id="10857" class="PrimitiveType">Set</a><a id="10860" class="Symbol">}</a> <a id="10862" class="Symbol">(</a><a id="10863" href="Assignment2.html#10863" class="Bound">x</a> <a id="10865" class="Symbol">:</a> <a id="10867" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10871" href="Assignment2.html#10851" class="Bound">A</a><a id="10872" class="Symbol">)</a> <a id="10874" class="Symbol">(</a><a id="10875" href="Assignment2.html#10875" class="Bound">y</a> <a id="10877" class="Symbol">:</a> <a id="10879" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10883" href="Assignment2.html#10853" class="Bound">B</a><a id="10884" class="Symbol">)</a> <a id="10886" class="Symbol">→</a> <a id="10888" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10890" href="Assignment2.html#10863" class="Bound">x</a> <a id="10892" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10894" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="10896" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10898" href="Assignment2.html#10875" class="Bound">y</a> <a id="10900" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10902" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10904" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10906" href="Assignment2.html#10863" class="Bound">x</a> <a id="10908" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="10914" href="Assignment2.html#10875" class="Bound">y</a> <a id="10916" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-⊎"></a><a id="10920" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10920" class="Postulate">∨-⊎</a> <a id="10924" class="Symbol">:</a> <a id="10926" class="Symbol">∀</a> <a id="10928" class="Symbol">{</a><a id="10929" href="Assignment2.html#10929" class="Bound">A</a> <a id="10931" href="Assignment2.html#10931" class="Bound">B</a> <a id="10933" class="Symbol">:</a> <a id="10935" class="PrimitiveType">Set</a><a id="10938" class="Symbol">}</a> <a id="10940" class="Symbol">(</a><a id="10941" href="Assignment2.html#10941" class="Bound">x</a> <a id="10943" class="Symbol">:</a> <a id="10945" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10949" href="Assignment2.html#10929" class="Bound">A</a><a id="10950" class="Symbol">)</a> <a id="10952" class="Symbol">(</a><a id="10953" href="Assignment2.html#10953" class="Bound">y</a> <a id="10955" class="Symbol">:</a> <a id="10957" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="10961" href="Assignment2.html#10931" class="Bound">B</a><a id="10962" class="Symbol">)</a> <a id="10964" class="Symbol">→</a> <a id="10966" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10968" href="Assignment2.html#10941" class="Bound">x</a> <a id="10970" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10972" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="10974" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10976" href="Assignment2.html#10953" class="Bound">y</a> <a id="10978" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="10980" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10982" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="10984" href="Assignment2.html#10941" class="Bound">x</a> <a id="10986" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="10992" href="Assignment2.html#10953" class="Bound">y</a> <a id="10994" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="10998" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#10998" class="Postulate">not-¬</a> <a id="11004" class="Symbol">:</a> <a id="11006" class="Symbol">∀</a> <a id="11008" class="Symbol">{</a><a id="11009" href="Assignment2.html#11009" class="Bound">A</a> <a id="11011" class="Symbol">:</a> <a id="11013" class="PrimitiveType">Set</a><a id="11016" class="Symbol">}</a> <a id="11018" class="Symbol">(</a><a id="11019" href="Assignment2.html#11019" class="Bound">x</a> <a id="11021" class="Symbol">:</a> <a id="11023" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11027" href="Assignment2.html#11009" class="Bound">A</a><a id="11028" class="Symbol">)</a> <a id="11030" class="Symbol">→</a> <a id="11032" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="11036" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11038" href="Assignment2.html#11019" class="Bound">x</a> <a id="11040" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11042" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11046" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="11049" href="Assignment2.html#11019" class="Bound">x</a> <a id="11051" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism]({{ site.baseurl }}/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
{% raw %}<pre class="Agda"><a id="11287" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="11299" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11299" class="Postulate Operator">_iff_</a> <a id="11305" class="Symbol">:</a> <a id="11307" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="11312" class="Symbol">→</a> <a id="11314" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="11319" class="Symbol">→</a> <a id="11321" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="11328" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11328" class="Postulate Operator">_⇔-dec_</a> <a id="11336" class="Symbol">:</a> <a id="11338" class="Symbol">∀</a> <a id="11340" class="Symbol">{</a><a id="11341" href="Assignment2.html#11341" class="Bound">A</a> <a id="11343" href="Assignment2.html#11343" class="Bound">B</a> <a id="11345" class="Symbol">:</a> <a id="11347" class="PrimitiveType">Set</a><a id="11350" class="Symbol">}</a> <a id="11352" class="Symbol">→</a> <a id="11354" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11358" href="Assignment2.html#11341" class="Bound">A</a> <a id="11360" class="Symbol">→</a> <a id="11362" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11366" href="Assignment2.html#11343" class="Bound">B</a> <a id="11368" class="Symbol">→</a> <a id="11370" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11374" class="Symbol">(</a><a id="11375" href="Assignment2.html#11341" class="Bound">A</a> <a id="11377" href="Assignment2.html#3474" class="Record Operator">⇔</a> <a id="11379" href="Assignment2.html#11343" class="Bound">B</a><a id="11380" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="11384" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2019/Assignment2.md %}{% raw %}#11384" class="Postulate">iff-⇔</a> <a id="11390" class="Symbol">:</a> <a id="11392" class="Symbol">∀</a> <a id="11394" class="Symbol">{</a><a id="11395" href="Assignment2.html#11395" class="Bound">A</a> <a id="11397" href="Assignment2.html#11397" class="Bound">B</a> <a id="11399" class="Symbol">:</a> <a id="11401" class="PrimitiveType">Set</a><a id="11404" class="Symbol">}</a> <a id="11406" class="Symbol">(</a><a id="11407" href="Assignment2.html#11407" class="Bound">x</a> <a id="11409" class="Symbol">:</a> <a id="11411" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11415" href="Assignment2.html#11395" class="Bound">A</a><a id="11416" class="Symbol">)</a> <a id="11418" class="Symbol">(</a><a id="11419" href="Assignment2.html#11419" class="Bound">y</a> <a id="11421" class="Symbol">:</a> <a id="11423" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="11427" href="Assignment2.html#11397" class="Bound">B</a><a id="11428" class="Symbol">)</a> <a id="11430" class="Symbol">→</a> <a id="11432" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11434" href="Assignment2.html#11407" class="Bound">x</a> <a id="11436" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11438" href="Assignment2.html#11299" class="Postulate Operator">iff</a> <a id="11442" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11444" href="Assignment2.html#11419" class="Bound">y</a> <a id="11446" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="11448" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11450" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="11452" href="Assignment2.html#11407" class="Bound">x</a> <a id="11454" href="Assignment2.html#11328" class="Postulate Operator">⇔-dec</a> <a id="11460" href="Assignment2.html#11419" class="Bound">y</a> <a id="11462" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
{% raw %}<pre class="Agda"><a id="11473" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
