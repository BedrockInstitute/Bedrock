<pre class="Agda"><a id="9" class="Symbol">{-#</a> <a id="13" class="Keyword">OPTIONS</a> <a id="21" class="Pragma">--cubical</a> <a id="31" class="Pragma">--safe</a> <a id="38" class="Pragma">--guardedness</a> <a id="52" class="Symbol">#-}</a>
<a id="56" class="Keyword">module</a> <a id="63" href="Sample.Use.html" class="Module">Sample.Use</a> <a id="74" class="Keyword">where</a>
</pre>
<!--en-->
# Using the input
<!--zh-->
# 使用输入
<!--ja-->
# 入力の利用
<!--/-->

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="Sample.Seed.html" class="Module">Sample.Seed</a> <a id="190" class="Keyword">using</a> <a id="196" class="Symbol">(</a> <a id="198" href="Sample.Seed.html#830" class="Datatype">Marker</a> <a id="205" class="Symbol">;</a> <a id="207" href="Sample.Seed.html#1183" class="Function">keep</a> <a id="212" class="Symbol">)</a>
</pre>
<!--en-->
We apply the earlier function twice. The [marker]{.term-ref #marker} link returns to its introduction.

## Two applications

The nested application exercises semantic expression selection.

**Definition** (`twice`{.Agda}) Two uses of `keep`{.Agda} still return the supplied value.
<!--zh-->
这里连续使用前面的函数两次。[标记]{.term-ref #marker}链接返回正式引入处。

## 两次应用

嵌套应用用于检验语义表达式的选择。

**定义** (`twice`{.Agda}) 两次使用 `keep`{.Agda}仍返回给定的值。
<!--ja-->
前の関数を二回適用する。[印]{.term-ref #marker}のリンクは導入箇所に戻る。

## 二回の適用

入れ子の適用で式の選択機能を検査する。

**定義** (`twice`{.Agda}) `keep`{.Agda}を二回用いても与えられた値が返る。
<!--/-->

<pre class="Agda"><a id="twice"></a><a id="811" href="Sample.Use.html#811" class="Function">twice</a> <a id="817" class="Symbol">:</a> <a id="819" href="Sample.Seed.html#830" class="Datatype">Marker</a> <a id="826" class="Symbol">→</a> <a id="828" href="Sample.Seed.html#830" class="Datatype">Marker</a>
<a id="835" href="Sample.Use.html#811" class="Function">twice</a> <a id="841" href="Sample.Use.html#841" class="Bound">value</a> <a id="847" class="Symbol">=</a> <a id="849" href="Sample.Seed.html#1183" class="Function">keep</a> <a id="854" class="Symbol">(</a><a id="855" href="Sample.Seed.html#1183" class="Function">keep</a> <a id="860" href="Sample.Use.html#841" class="Bound">value</a><a id="865" class="Symbol">)</a>
</pre>
∎

<!--en-->
The ordinary [earlier chapter](Sample.Seed.html) link remains a normal page link.
<!--zh-->
普通的[前章](Sample.Seed.html)链接仍然直接跳转页面。
<!--ja-->
通常の[前章](Sample.Seed.html)リンクはページへ移動する。
<!--/-->
