# Lean検証で見つかった論文上の穴・要補足点メモ
## fixed-h CFG / TCS-D-26-00494

更新日: 2026-09-11  
対象: *Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing*  
目的: Lean形式化の過程で見つかった「数学的な穴」「証明上の暗黙条件」「記述を強化した方がよい箇所」を、査読対応・改訂用に継続記録する。

形式化全体の進捗は [`FORMALIZATION_FIXEDH.md`](./FORMALIZATION_FIXEDH.md) を参照。

---

## 0. 現時点の総評

現時点では、**主要定理そのものが崩れるような反例や致命的欠陥は見つかっていない**。

一方で Lean 形式化によって、紙面では自然言語で流していた箇所のうち、

- 実際には追加の不変量が必要な箇所
- 局所補題の statement がそのままでは一般に真でない箇所
- 「最小性」の意味を正確に区別しないと証明が閉じない箇所
- trimming の順序を明示しないと不変量が壊れる箇所
- 抽象補題から実際の typed grammar への bridge を明示すべき箇所

が見えてきた。

したがって、現状は「主定理の崩壊」ではなく、**local statement repair / proof gap / hidden invariant / exposition gap の補修**という性格が強い。

---

# 1. Theorem 5.6 の soundness では membership だけでなく型保存不変量が必要

### 該当箇所
Section 5, learner soundness（Theorem 5.6）

### Leanで必要になった強い不変量
帰納法を閉じるには

\[
[x:u,v]\Rightarrow^* y
\quad\Longrightarrow\quad
u y v\in L
\ \land\
h(y)=h(x)
\]

という二成分の不変量が必要。

特に Rule (2), Rule (3) で h-substitutability を適用する際、`h(y)=h(x)` が次の帰納段階に必要になる。

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
`[x:u,v] → [x:u',v']` の後、`[x:u',v'] ⇒* y` とする。

帰納法から

\[
u' y v'\in L,\qquad h(y)=h(x)
\]

を得る。

さらにサンプルから

\[
u'xv'\in K\subseteq L,\qquad uxv\in K\subseteq L
\]

なので、\((u',v')\) と \((u,v)\) はともに \(D_L(x)\) に属する。

ここで \(h(y)=h(x)\) と共通 context の存在を用いて h-substitutability を適用し、

\[
D_L(x)=D_L(y)
\]

を得て初めて \(uyv\in L\) が従う。

### 判定
**proof detail omitted / exposition gap**

### 数学的影響
なし。証明の論理ステップを明示すべき。

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

を使い、anchor nonterminal から Rule (4) で直接 terminal `a` を生成する議論になっている。

しかし、同一の typed nonterminal \(X\) に複数の terminal rule がある場合、これは一般には成り立たない。

たとえば trivial observer の下で同じ state に

\[
X\to a,\qquad X\to b
\]

があれば、\(\omega(X)\) は shortlex 最小の terminal yield でしかなく、任意の terminal production の右辺に一致するとは限らない。

### Leanで通った修正版
主定理を変える必要はない。terminal rule \(X\to a\) に対して

1. anchor observation から `[omega(X):u_X,v_X]` を得る
2. rule observation から `[a:u_X,v_X]` を得る
3. Lemma 4.6 と typed terminal rule から
   \[
   h(\omega(X))=h(a)
   \]
   を得る
4. Rule (3) で
   `[omega(X):u_X,v_X] → [a:u_X,v_X]`
5. Rule (4) で `[a:u_X,v_X] → a`

とすればよい。

### 判定
**local statement/proof error**

### 数学的影響
**Theorem 5.5, Theorem 5.7, Corollary 5.8 は修復可能であり、Lean では修正版で通過済み。**

### 優先度
**最優先で原稿修正**

### 対応状況
**fixed in Lean / open in manuscript**

---

# 4. branching CFG の typed refinement では productive-first trimming が必要

### 該当箇所
Section 4 の typed refinement / trimming 周辺

### 問題
branching rule を typed refinement するとき、非生産的な parent state を残したまま context 情報を下向きに伝播すると、その parent が実際には terminal yield を持たないにもかかわらず、誤った yield type を前提とした outer-context frame が productive child に伝わりうる。

### 安全な順序
1. まず productive states を確定する
2. 非生産的 state/rule を落とす
3. その後 reachable / context-side trimming を行う

つまり **productive-first trimming** が必要。

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
Section 7, Lemma 7.6（canonical context の長さ評価）

### 重要な発見
canonical context \(\chi(X)\) は \(|u|+|v|\) を最小化した context として定義されているわけではない。

Section 4 で定義した

1. 各 word の shortlex
2. context pair 上の lexicographic extension

に関する最小元である。

したがって

> cycle を消すと context の総長が短くなるので minimality に反する

だけでは、そのままでは証明にならない。

### Leanで必要になった補題
cycle deletion 後の context \((u',v')\) について直接

\[
(u',v') <_{\mathrm{ctx\text{-}shortlex}} (u,v)
\]

を示す必要がある。

場合分けは概ね次の通り。

- deletion が left context を短くする
  → left word が shortlex-smaller
  → pair 全体も smaller
- left context が変わらず right context が短くなる
  → right word が shortlex-smaller
  → pair 全体も smaller

### 判定
**substantive proof gap**

### 数学的影響
定理自体が偽という意味ではなく、order-theoretic argument の不足。

### 優先度
**高**

### 対応状況
**Lean proof in progress / open in manuscript**

---

# 6. Section 7 の cycle-deletion argument は generic spine lemma と typed grammar の bridge が必要

### 該当箇所
Lemmas 7.3–7.6, Proposition 7.7

### Leanで分離された構造
形式化ではまず

- generic strict-linear grammar
- derivation spine
- repeated state の deletion
- simple spine の長さ bound
- canonical shortlex witness

を抽象的に証明している。

しかし論文の対象は typed refinement 後の retained grammar \(H\)。したがって最終的には

> retained typed grammar \(H\) が generic strict-linear formalization の仮定を満たす

という bridge lemma が必要。

### 判定
**bridge obligation / exposition gap**

### 対応状況
**generic side fixed in Lean / typed end-to-end bridge open**

---

# 7. Prop-valued derivation proof から spine を計算する設計は Lean ではそのまま通らない

### 該当箇所
Lean 実装上の問題。数学的な穴ではない。

### 最初の失敗
`LinearDerives` や `LinearOccurs` を Prop-valued inductive relation として定義し、その proof term に再帰して

- `spine : List W`
- `depth : Nat`

などの data を抽出しようとした。

Lean では Prop-valued inductive の eliminator は原則として computational data へ除去できないため、この設計では直接取り出せなかった。

### 解決
spine を明示的な index / witness として持たせる設計に変更。

### 判定
**formalization-only architecture issue**

### 数学的影響
なし。

### 対応状況
**fixed in Lean**

---

# 8. Lemma 7.5 の yield-length bound は simple spine への変換を明示した方がよい

### 該当箇所
Section 7, Lemma 7.5

### Leanで明確になった証明構造
\[
|\omega(X)|\le |W|
\]

を得るには、次の流れが明確。

1. canonical yield の derivation を取る
2. repeated state があれば cycle deletion でより短い yield を作る
3. shortlex minimality に反する
4. よって canonical derivation spine は simple
5. simple spine の state 数は \(|W|\) 以下
6. strict-linear rule は各 step で terminal を高々 1 個追加
7. よって yield length も \(|W|\) 以下

### 判定
**proof structure should be made explicit**

### 対応状況
**fixed in Lean / manuscript exposition can be strengthened**

---

# 9. Section 7 の length bounds と characteristic-sample bounds は別レイヤとして扱うべき

### Leanで分離した内容

#### combinatorial layer
- typed state 数
- typed rule 数
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

特に「状態数 bound」から「sample-size / total-length bound」への移行を一段ずつ書くと、polynomial time-and-data の主張が追いやすい。

---

# 10. 現時点で Lean が否定していないもの

現時点の検証では、少なくとも以下について「定理が偽である」という結果は出ていない。

- Theorem 5.6 soundness
- typed refinement の基本的不変量
- exact manuscript characteristic sample からの reconstruction の中核
- Theorem 5.5 completeness（上記 terminal case 修正版）
- Theorem 5.7 exact reconstruction
- Corollary 5.8 identification in the limit
- Section 6 の polynomial envelope の算術・組合せ部分
- Section 7 の strict-linear cycle deletion
- simple-spine bounds
- finite counting envelopes

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

# 11. 改訂優先順位

## A. 必ず直したい
1. **Lemma 5.2(i) terminal case** の `omega(X)=a` を使う箇所を修正する。
2. **Lemma 7.6** を total-length minimality ではなく lexicographic-shortlex minimality に沿った cycle-deletion proof にする。
3. **Section 4 trimming** の productive-first 性を明記する。
4. **Theorem 5.6** で
   \[
   uyv\in L \land h(y)=h(x)
   \]
   の強い帰納法不変量を明記する。

## B. できれば直したい
5. Rule (2)/(3) の soundness で distribution equality を得るステップを詳述する。
6. Section 7 の generic strict-linear lemma と actual typed grammar \(H\) の bridge を明示する。
7. Lemma 7.5–7.7 を `simple spine → length bound → sample bound` の順に構造化する。

---

# 12. 今後の追記フォーマット

Lean検証で新しい問題を見つけたら以下の形式で追記する。

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

# 13. 現在の結論

Lean検証は、現段階では論文を壊す方向ではなく、**紙面上の証明をより査読耐性の高い形に研ぎ澄ます方向に効いている**。

特に重要なのは

- Lemma 5.2(i) の terminal case 修正
- soundness の型保存不変量
- productive-first trimming
- Lemma 7.6 の lexicographic-shortlex minimality

の4点。

これらは次回の TCS 原稿改訂時に paper-side へ反映する価値が高い。
