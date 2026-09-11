# Lean検証で見つかった論文上の穴・要補足点メモ
## fixed-h CFG / TCS-D-26-00494

更新日: 2026-09-11  
対象: *Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing*  
目的: Lean形式化の過程で見つかった「数学的な穴」「局所 statement の不備」「証明上の暗黙条件」「記述を強化した方がよい箇所」を、査読対応・改訂用に継続記録する。

形式化全体の進捗は [`FORMALIZATION_FIXEDH.md`](./FORMALIZATION_FIXEDH.md) を参照。

---

## 0. 現時点の総評

現時点では、**主要定理そのものが崩れるような反例や致命的欠陥は見つかっていない**。

一方で Lean 形式化によって、以下が明確になった。

- 実際には追加の不変量が必要な箇所
- 局所補題の statement / proof がそのままでは一般に正しくない箇所
- 「最小性」の意味を正確に区別しないと証明が閉じない箇所
- trimming の順序を明示した方が安全な箇所
- 抽象補題から実際の typed grammar への bridge を明示すべき箇所
- 有限モノイドで cancellation を暗黙に仮定しているように読める counting argument

したがって、現状は「主定理の崩壊」ではなく、**local statement repair / proof gap / hidden invariant / exposition gap の補修**という性格が強い。

---

# 1. Theorem 5.6 の soundness では membership だけでなく型保存不変量が必要

### 該当箇所
Section 5, learner soundness（Theorem 5.6）

### Leanで必要になった強い不変量
帰納法を閉じるには

\[
[x:u,v]\Rightarrow^* y
\Longrightarrow
uyv\in L\ \land\ h(y)=h(x)
\]

という二成分の不変量が必要。

特に Rule (2), Rule (3) で h-substitutability を適用する際、`h(y)=h(x)` が帰納段階に必要になる。

### 判定
**hidden invariant / exposition gap**

### 数学的影響
主定理の修正は不要。

### 改訂候補
> We prove the stronger invariant that every terminal yield \(y\) derived from \([x:u,v]\) satisfies both \(uyv\in L\) and \(h(y)=h(x)\).

### 対応状況
**fixed in Lean / open in manuscript**

---

# 2. Rule (2) の soundness は context transport だけでなく distribution equality を一段使う

### 該当箇所
Section 5, learner Rule (2)

### Leanで明示された依存関係
`[x:u,v] → [x:u',v']`、`[x:u',v'] ⇒* y` とする。
帰納法から

\[
u'yv'\in L,\qquad h(y)=h(x)
\]

を得る。さらに sample から `u'xv', uxv ∈ K ⊆ L` なので、必要な共通 context が得られる。ここで h-substitutability を適用して

\[
D_L(x)=D_L(y)
\]

を得て初めて `uyv ∈ L` が従う。

### 判定
**proof detail omitted / exposition gap**

### 数学的影響
なし。

### 対応状況
**fixed in Lean / open in manuscript**

---

# 3. Lemma 5.2(i) の terminal case は現行 statement のままでは一般に真でない

### 該当箇所
Section 5, Lemma 5.2(i) および Theorem 5.5 の高さ 1 の terminal case

### 現行原稿の問題
任意の realized terminal rule

\[
X\to a
\]

に対して、原稿は実質的に

\[
\omega(X)=a
\]

を用いている。しかし同一の typed nonterminal \(X\) に複数の terminal rule がある場合、これは一般には成り立たない。

たとえば trivial observer の下で同じ state に `X→a` と `X→b` があれば、\(\omega(X)\) は shortlex 最小の terminal yield でしかなく、任意の terminal production の右辺に一致するとは限らない。

### Leanで通った修正版
主定理は変更不要。terminal rule \(X\to a\) に対して

1. anchor から `[omega(X):u_X,v_X]` を得る
2. rule observation から `[a:u_X,v_X]` を得る
3. Lemma 4.6 と typed terminal rule から `h(omega(X))=h(a)` を得る
4. Rule (3) で `[omega(X):u_X,v_X] → [a:u_X,v_X]`
5. Rule (4) で `[a:u_X,v_X] → a`

とする。

### 判定
**local statement/proof error**

### 数学的影響
**Theorem 5.5, Theorem 5.7, Corollary 5.8 は修復可能であり、Lean では修正版で通過済み。**

### 優先度
**最優先で原稿修正**

### 対応状況
**fixed in Lean / open in manuscript**

---

# 4. branching CFG の typed refinement では productive-first trimming を明示した方が安全

### 該当箇所
Section 4 の typed refinement / trimming 周辺

### 問題
branching rule では、非生産的な parent typed state を経由して outer-context frame を伝播させると、productive child に不適切な inherited frame が残る危険がある。

### 安全な順序
1. productive states を確定する
2. 非生産的 state/rule を除く
3. その後 reachable / context-side trimming を行う

つまり **productive-first trimming** を明示する。

### 判定
**important hidden algorithmic condition / exposition gap**

### 数学的影響
定理そのものより trimming 手順の明示性の問題。

### 改訂候補
> The trimming is performed productively first: nonproductive typed states are removed before outer-context information is propagated.

### 対応状況
**reflected in formalization design / open in manuscript**

---

# 5. Lemma 7.6 の minimality は total context length の最小性ではない

### 該当箇所
Section 7, Lemma 7.6

### 現行原稿の問題
canonical context \(\chi(X)\) は \(|u|+|v|\) の最小元として定義されているのではなく、Section 4 の

1. word shortlex
2. context pair 上の lexicographic extension

に関する最小元である。

したがって

> cycle を消すと total context length が短くなるので minimality に反する

だけでは、そのままでは証明にならない。

### Leanで証明した修正版
cycle deletion 後の context \((u',v')\) について直接

\[
(u',v') <_{\mathrm{ctx\text{-}shortlex}} (u,v)
\]

を証明する。

- left context が短くなれば left word 自体が shortlex-smaller
- left が同じで right context が短くなれば right word が shortlex-smaller

という場合分けで、実際の context order に対する minimality contradiction を得る。

### 判定
**substantive proof gap, repairable**

### 数学的影響
Lemma 7.6 の statement は維持できる。証明だけを補強すればよい。

### 優先度
**高**

### 対応状況
**fixed in Lean (`LinearShortlex.lean`, focused CI green) / open in manuscript**

---

# 6. Proposition 7.7(ii) の `q determined by h(a)` という counting 説明は有限モノイド一般では不正確

### 該当箇所
Section 7, Proposition 7.7(ii)

### 現行原稿の問題
原稿では、各 linear source production の typed copies を

> over \(m,n,p\in M\) with the appropriate \(q\) determined by \(h(a)\)

と数えている。

しかし有限モノイドは一般に cancellation を持たない。たとえば

\[
p=h(a)q
\]

から \(p\) と \(h(a)\) を固定しても \(q\) は一意には決まらない。同様に \(p=qh(a)\) でも一意性はない。

### 正しい counting parameterization
bound 自体はそのまま成立する。\(q,m,n\in M\) を自由パラメータとして取り、parent yield type \(p\) を

- `A → aB` なら \(p=h(a)q\)
- `A → Ba` なら \(p=qh(a)\)

と**前向きに決定**すればよい。

したがって source production 1本につき高々 \(|M|^3\) slots であり、

\[
|R|=O(|P_0||M|^3)
\]

は維持される。

### Leanでの対応
`LinearTypedRuleSlot := P × M × M × M` として `(production,q,m,n)` を slot にし、parent type を forward multiplication で構成する形式化を導入した。

### 判定
**local proof/exposition error; theorem bound survives**

### 数学的影響
Proposition 7.7(ii) の結論は変更不要。証明中の parameterization の文言を修正するだけでよい。

### 優先度
**中〜高**

### 対応状況
**fixed by design in Lean / CI verification in progress / open in manuscript**

---

# 7. Section 7 の generic spine lemma と actual typed grammar \(H\) の bridge が必要

### 該当箇所
Lemmas 7.3–7.6, Proposition 7.7

### Leanで分離された構造
まず generic strict-linear grammar 上で

- derivation / occurrence spine
- repeated state の deletion
- simple-spine length bound
- shortlex minimality

を証明した。

論文の対象は typed refinement 後の retained grammar \(H\) なので、最終的には source SSLNF grammar と fixed monoid typing から、generic strict-linear object への bridge が必要。

### 現在の形式化
`LinearTypedRefinement.lean` で source production index を持つ SSLNF presentation から actual fixed-h typed linear grammar を構成し、

- yield type invariant
- outer context type invariant
- retained typed-state bound

まで接続済み。

### 判定
**bridge obligation / exposition gap**

### 対応状況
**full typed-linear bridge green in Lean; reachable/productive trim and final Prop. 7.7/7.8 connection in progress**

---

# 8. Prop-valued derivation proof から spine を計算する設計は Lean ではそのまま通らない

### 該当箇所
Lean 実装上の問題。数学的な穴ではない。

### 最初の失敗
`LinearDerives` / `LinearOccurs` を Prop-valued inductive relation とし、その proof term から `List W` や `Nat` を直接抽出しようとすると、Prop elimination restriction に当たる。

### 解決
spine を明示的な index / witness として持つ relation に変更。

### 判定
**formalization-only architecture issue**

### 数学的影響
なし。

### 対応状況
**fixed in Lean**

---

# 9. Lemma 7.5 の yield-length bound は simple spine への変換を明示した方がよい

### 該当箇所
Section 7, Lemma 7.5

### Leanで明確になった証明構造

1. canonical yield の derivation を取る
2. repeated state があれば cycle deletion でより短い yield を作る
3. shortlex minimality に反する
4. よって canonical derivation spine は simple
5. simple spine の state 数は \(|W|\) 以下
6. strict-linear rule は各 step で terminal を1個ずつ寄与する
7. よって \(|\omega(X)|\le |W|\)

### 判定
**proof structure should be made explicit**

### 対応状況
**fixed in Lean / manuscript exposition can be strengthened**

---

# 10. Section 7 の length bounds と characteristic-sample bounds は別レイヤとして扱うと明瞭

### Leanで分離した内容

#### combinatorial layer
- typed state / rule 数
- simple spine 長
- canonical yield/context 長

#### sample layer
- anchor 数
- rule witness 数
- optional epsilon
- 各 witness word の長さ
- total symbol count

### 判定
**not a gap; exposition improvement**

---

# 11. 現時点で Lean が否定していないもの

現時点で「定理が偽」と判定された主結果はない。少なくとも以下は機械検証の中心線に乗っている。

- Theorem 5.6 soundness
- typed refinement の基本的不変量
- exact manuscript characteristic sample からの reconstruction の中核
- Theorem 5.5 completeness（terminal case 修正版）
- Theorem 5.7 exact reconstruction
- Corollary 5.8 identification in the limit
- Section 6 の polynomial envelope の算術・組合せ部分
- Section 7 の strict-linear cycle deletion
- Lemma 7.5 の shortlex yield-length bound
- Lemma 7.6 の actual context-shortlex に基づく修正版 proof
- finite state/sample counting envelopes

したがって現在見つかっている問題の中心は

\[
\text{false main theorem}
\]

ではなく

\[
\text{local proof error / missing proof detail / hidden invariant / bridge obligation}
\]

である。

---

# 12. 改訂優先順位

## A. 必ず直したい
1. **Lemma 5.2(i) terminal case** の `omega(X)=a` を使う箇所を修正する。
2. **Lemma 7.6** を total-length minimality ではなく lexicographic-shortlex minimality に沿った proof にする。
3. **Section 4 trimming** の productive-first 性を明記する。
4. **Theorem 5.6** の強い帰納法不変量を明記する。

## B. かなり直したい
5. **Proposition 7.7(ii)** の parameterization を `(p,m,n) with q determined` ではなく `(q,m,n) with p determined by multiplication` に直す。
6. Rule (2)/(3) の soundness で distribution equality を得るステップを詳述する。
7. Section 7 の generic strict-linear lemma と actual typed grammar \(H\) の bridge を明示する。
8. Lemma 7.5–7.7 を `simple spine → length bound → sample bound` の順に構造化する。

---

# 13. 今後の追記フォーマット

### [番号] タイトル
- **該当箇所**:
- **Leanで止まった点**:
- **必要になった追加仮定・補題**:
- **数学的影響**:
  - theorem false
  - local statement error
  - proof gap
  - hidden assumption
  - exposition gap
  - formalization-only issue
- **修正案**:
- **CI / commit**:
- **対応状況**: open / fixed in Lean / fixed in manuscript

---

# 14. 現在の結論

Lean検証は、現段階では論文を壊す方向ではなく、**紙面上の証明をより査読耐性の高い形に研ぎ澄ます方向に効いている**。

特に paper-side で重要なのは、

- Lemma 5.2(i) の terminal case 修正
- Theorem 5.6 の型保存不変量
- productive-first trimming
- Lemma 7.6 の lexicographic-shortlex minimality
- Proposition 7.7(ii) の monoid parameterization

の5点。
