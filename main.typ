#import "template.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#show: thmrules

#let uprsans(X) = $upright(sans(#X))$

#let theory(c) = $uprsans(#c)$

#let Robinson = $theory("Q")$
#let Ind(X)   = $theory("I")#X$
#let Peano    = $theory("PA")$
#let EA    = $theory("EA")$

#let num(x) = $overline(#x)$

#let out(x) = $dot(#x)$

#let GL = $theory("GL")$
#let GLP = $theory("GLP")$

#let dia = $class("unary", lozenge.stroked)$
#let box = $class("unary", square.stroked.medium)$

#let Proof(T) = $"Proof"_#T$ 
#let witness(T) = $attach(lt.tri.eq, br: #T)$
#let Box(T) = $box_#T$ 
#let Dia(T) = $dia_#T$ 

#let ht(x) = $lr(| #x |)$ 

#let solovay = $sans("S")$

#show: project.with(
  title: [算術的完全性],
  authors: ("Palalansoukî",),
  repo: "https://github.com/iehality/notes-on-arithmetical-completeness",
)

Solovay による $GL$ の算術的完全性を証明する． 
これはしばしば「「そこに留まらない」と証明出来た場所に移動する点」の移動を記述する原始再帰的関数を構成することで証明されるが，
これは形式的には煩雑なので，ここでは明示的に対角化補題を用いて示す．
証明にあたって @boolos1995logic や @proof-truth の第五章を参考にした．

#outline(indent: auto,)

= Preliminaries

== 算術

$T$ を r.e.理論とする．
$Box(T)(x)$ を通常の可証性述語とする． また $Dia(T)(x) := not Box(T)(godel(not out(x)))$ とする．
しばしば $Box(T)(godel(phi))$ を $Box(T) phi$ のように書く．
$$

#definition[
  論理式 $x witness(T) y$ は 「$x$ は $y$ のいかなる $T$-証明よりも小さい $T$-証明を持つ」ことを意味する．
  $
    x witness(T) y := exs(z) [Proof(T)(z, x) and fal(w <= z)[not Proof(T)(w, y)]]
  $
]

しばしば $godel(phi) witness(T) godel(psi)$ を $phi witness(T) psi$ のように略記する． 次の補題は定義から簡単に従う．

#lemma[
  次が $EA$ で証明可能．
  1. $Box(T) x <-> x witness(T) x$
  2. $x witness(T) y and y witness(T) z -> x witness(T) z$
  3. $x witness(T) y and y witness(T) x -> x = y$
]

#lemma[
  有限集合 $u$ に添え字付けられた論理式 ${phi_i}_(i in u)$ について，
  $
    EA proves (or.big_(i in u) Box(T) phi_i) -> (or.big_(i in u) and.big_(j in u) phi_i witness(T) phi_j)
  $
]<lemma:search-minimal-proof>
#proof[
  各 $k in u$ について次の証明を行う： $Box(T) phi_k$ であると仮定する．
  $EA$ の内部で作業する．
  $
    psi(x) := or.big_(i in u) Proof(T)(x, godel(phi_i))
  $
  と定める． $Box(T) phi_i$ より $exs(z) psi(z)$ であるから， minimalization より
  #footnote[
    なのでベース論理 + $Sigma^upright("b")_2$-帰納法があれば示せる．]
  $psi(w)$ を満たす最小の $w$ が存在する．
  $psi(w)$ の場合分けを行う． 各 $i in W$ について次の証明を行う．
  #struct[
    仮定より $Proof(T)(w, godel(phi_i))$ かつ $w$ は $psi$-最小. よってすべての $j in u$ について $phi_i witness(T) phi_j$.
  ]
]

#let height(x) = $"height"(#x)$

$Box(T)^n phi$ を $Box(T)$ の $n$ 回反復 $underbrace(Box(T) Box(T) ... Box(T), n) phi$ とする．
理論の高さ $height(T) < omega + 1$ を次のように定める．

#definition[
  $
    height(T) :=
    cases(
      n & "minimal" n "such that" T proves Box(T)^n bot,
      omega & "if" T nproves Box(T)^n bot "for all" n)
  $
]

$T$ が $Sigma_1$-健全ならば明らかに $height(T) = omega$.

== Kripke モデル

#definition[
  次を満たす推移的 Kripke フレーム $(W, prec, r)$ を根付き推移的 Kripke フレームという．
  - $r in W$ かつすべての $x in W without {r}$ について $r prec x$.
  同様に根付き Kripkeモデルも定義する．
]

#definition[
  根付き推移的 Kripke モデル $(W', prec', r', V')$ を次のように拡張したモデル $(W, prec, r, V)$ を単純拡大モデルという．
  $r$ を $W'$ に含まれない要素とする．
  $
    W &:= W' union {r}\
    (prec) &:= (prec') union {(r, i) | i in W'} \
    i V p &:<=> cases(
      r' V' p & " if" i = r,
      i V' p & " if" i in W')      
  $
]

#definition[
  $GL$ の有限 Kripke フレーム $F := (W, prec)$ の高さを $ht(F)$ と書く． $(prec)$ が明らかなときは単に $ht(W)$ と書く．
]

== 鎖

$W$ を集合， $prec$ を $W$ 上の二項関係とする．

#definition[
  $i$ から $j$ までの有限 $prec$-鎖の集合 $"Chain"(i, j)$ を帰納的に定める．
  $
    i in W &==> brak(i) in "Chain"(i, i)\
    epsilon in "Chain"(i, j) "and" j prec k &==> epsilon paren.t brak(k) in "Chain"(i, k)
  $
]

#lemma[
  $prec$ が非反射的かつ推移的なとき， $W$ が有限ならば $"Chain"(i, j)$ も有限.
  ]

= $GL$ の算術的完全性

少し一般化した形で示す．

#theorem[
  $T$ を $EA$ を含む算術の r.e.理論とする．$GL$ の論理式 $A$ について
  $
    GL + box^(height(T)) bot proves A <==> fal(f.) T proves A^f
  $
]<thm:arith-comp>

ただし $box^omega bot := top$ とする．

$(==>)$ 方向は $EA$ が Hilbert-Berneys-Löb 可証性条件を満たすことから従う． $(<==)$ 方向は以下の戦略によって示す．

$GL nproves A ==> exs(f) EA nproves A^f$ を示せば良い． 仮定より $A$ の反例となる $GL + box^(height(T)) bot$ の Kripke モデル $(W', prec', r', V')$ が存在する． 
その単純拡大モデル $(W, prec, r, V)$ を得る．
$W, r' nmodels A $ としてよい．
また $W', i models box^(height(T)) bot$ より $ht(W) -1 = ht(W') <= height(T)$ である．

これを用いて次を満たす Solovay 文 ${solovay_i}_(i in W)$ を構成する．この構成方法は後節で示す（@lemma:solovay-main-lemma）．

1. $i != j$ ならば $EA proves solovay_i -> not solovay_j$
2. $i prec j$ ならば $EA proves solovay_i -> Dia(T) solovay_j$
3. $r prec i$ ならば $EA proves solovay_i -> Box(T) (or.big_(j succ i) solovay_j)$
4. $EA proves or.big_(i in W) solovay_i$

変換 $*$ を以下から生成されるものとして定める．
$
  p^* := or.big_(i V p) solovay_i
$

このとき次が証明可能．

#lemma[
  すべての論理式 $B$, $i succ r$ について，
  $
    W, i models B ==> EA proves solovay_i -> B^*
  $
]<lemma:proves-of-models>
#proof[
  次を $B$ に関する帰納法で示す． $B$ は否定標準形を取っているとする．

  / $B = p$ のとき:\
    仮定より $i V p$ なので $solovay_i -> or.big_(j V p) solovay_j$ はトートロジー．
  / $B = not p$ のとき:\
    仮定より $solovay_i$ は $p^* = or.big_(j V p) solovay_j$ に含まれないので， 条件1 より証明可能．
  / 論理結合子:\ 略
  / $B = box C$ のとき:\
    帰納法の仮定より， $i prec j$ となるすべての $j$ について $EA proves solovay_j -> C^*$
    よって $EA proves or.big_(j succ i) solovay_j -> C^*$.
    可証性条件より $EA proves Box(T)(or.big_(j succ i) solovay_j -> C^*)$.
    また条件3と再び可証性条件より $EA proves solovay_i -> Box(T) C^*$.
  / $B = dia C$ のとき:\
    帰納法の仮定より $i prec j$ であるような $j$ で $EA proves solovay_j -> C^*$ を満たすものが存在する．
    可証性条件より $EA proves Dia(T) solovay_j -> Dia(T) C^*$.
    したがって条件2より $EA proves solovay_i -> Dia(T) C^*$.
]

ここで $(<==)$ 方向を示す．

#proof[(@thm:arith-comp)][
  まず $EA proves Dia(T)^(ht(W)) top -> solovay_r$ が成り立つ．
  #struct[
    $i succ r$ について， $W, i models box^ht(W) bot$ であるから @lemma:proves-of-models より $EA proves solovay_i -> Box(T)^ht(W) bot$.
    よって $EA proves Dia(T)^ht(W) top -> and.big_(i succ r) not solovay_i$.
    従って条件 4. より $EA proves Dia(T)^ht(W) top -> solovay_r$.
  ]
  また条件2より $EA + Dia(T)^(ht(W)) top proves Dia(T) solovay_(r')$.
  @lemma:proves-of-models より $EA proves solovay_(r') -> not A^*$ だから $EA + Dia(T)^(ht(W)) top proves Dia(T) not A^*$,
  よって $EA + Dia(T)^(ht(W)) top proves not Box(T) A^*$.
  したがって $T proves A^*$ ならば $EA proves Box(T)^(ht(W)) bot$,
  $EA$ の $Sigma_1$-健全性より $T proves Box(T)^(ht(W) - 1) bot$ だが， これは $ht(W) - 1 <= height(T)$ と矛盾する↯．

]


== Solovay 文

$(W, prec, r)$ を 根付き-有限-非反射-推移的 Kripke フレームとする．

#let FunH = $sans("H")$

#definition[
  $W$ の有限 $prec$-鎖 $epsilon$ について， ${x_i}_(i in W)$ のみを自由変数として持つ論理式 $FunH_(epsilon)$ を定める．
  $
    FunH_brak(i) &:= top\
    FunH_(epsilon paren.t brak(i, j)) &:= 
      FunH_(epsilon paren.t brak(i)) and and.big_(k succ i) godel(not out(x_j)) witness(T) godel(not out(x_k))\
  $
  また $i in W$ について $FunH_(i)$ を次のように定義する．
  $
    FunH_(i) := or.big_(epsilon in "Chain"(r, i)) FunH_epsilon
  $
]
$Phi({t_j \/ x_j}_(j in u))$ は式 $Phi$ に現れる $u$ で添え字づけられた各自由変数 $x_j$ に $t_j$ を代入した結果を表す表記とする．
#definition[Solovay 文][
  対角化補題により次のような文のあつまり ${solovay_i}_(i in W)$ が定義できる．
  $
    EA proves solovay_i <-> FunH_(i)({godel(solovay_j) \/ x_j}_(j in W) ) and and.big_(k succ i) Dia(T)solovay_k
    " for all" i in W
  $
]<def:construct-solovay>

以降 $FunH_(epsilon)({godel(solovay_j) \/ x_j}_(j in W))$ や $FunH_(i)({godel(solovay_j) \/ x_j}_(j in W))$
を単に $FunH_epsilon$, $FunH_(i)$ と略記する
#footnote[
    $FunH_i$ は， @boolos1995logic や @proof-truth の証明における関数 $h$ について
    $h$ の値域が $i$ を通過することを意味する論理式 $exs(n) h(n) = i$ に対応する論理式である．
]． これらが共に $Sigma_1$-論理式であることに注意せよ．

#lemma[
  1. 比較不能な $epsilon_1 in "Chain"(r, i_1), epsilon_2 in "Chain"(r, i_2)$ について，
    $EA proves FunH_(epsilon_1) -> not FunH_(epsilon_2)$
  2. $i succ 0$ について $EA proves solovay_i -> Box(T) not solovay_i$
  3. $i in W$ について $EA proves FunH_i -> solovay_i or or.big_(j succ i) solovay_j$.
]<lemma:FunH>
#proof[
  1. 比較不能性よりある $epsilon in "Chain"(r, i)$ と
    $epsilon paren.t brak(j_1) subset.eq epsilon_1$, $epsilon paren.t brak(j_2) subset.eq epsilon_2$
    であるような相異なる $j_1, j_2 in W$ が存在する．
    $EA$ の内部で作業する． $FunH_(epsilon_1), FunH_(epsilon_2)$ を仮定すると， その定義より
    $FunH_brak(i, j_1)$, $FunH_brak(i, j_2)$ が従う．
    よって $not solovay_(j_1) witness(T) not solovay_(j_2)$ かつ $not solovay_(j_2) witness(T) not solovay_(j_1)$
    なので反対称性より $j_1 = j_2$ ↯.
  2. ある $i' prec i$, $epsilon'$ について $epsilon = epsilon' paren.t brak(i', i)$.
    $EA proves FunH_epsilon -> FunH_brak(i', i)$ より $EA proves FunH_epsilon -> Box(T) not solovay_i$.
  3. $i$ の高さに関する帰納法で示す．
    すべての $j succ i$ について $EA proves FunH_j -> solovay_j or or.big_(k succ j) solovay_k$ であると仮定する．
    $EA$ の内部で作業する． $FunH_i$ と $not solovay_i$ を仮定し $or.big_(j succ i) solovay_j$ が従うことを示せばよい．
    #struct[
      $not solovay_i$ より $or.big_(j succ i) Box(T) not solovay_j$ であるから， @lemma:search-minimal-proof より
      ある $j succ i$ について $and.big_(j' succ i) not solovay_j witness(T) not solovay_(j')$, 
      すなわち $FunH_brak(i, j)$ が成り立つ．
      よって $FunH_j$ なので帰納法の仮定より $solovay_j or or.big_(k succ j) solovay_k$.
    ]
]

#lemma[
  1. $i != j$ ならば $EA proves solovay_i -> not solovay_j$.
  2. $i prec j$ ならば $EA proves solovay_i -> Dia(T) solovay_j$.
  3. $r prec i$ ならば $EA proves solovay_i -> Box(T) (or.big_(j succ i) solovay_j)$.
  4. $EA proves or.big_(i in W) solovay_i$.
]<lemma:solovay-main-lemma>
#proof[
  1. すべての
    $epsilon_i in "Chain"(r, i), epsilon_j in "Chain"(r, j)$ について次を示せば良い．
    $
      EA proves
        not (FunH_(epsilon_i) and FunH_(epsilon_j) and
          and.big_(k succ i) Dia(T) solovay_k and and.big_(l succ j) Dia(T) solovay_l)
    $
    $epsilon_i, epsilon_j$ が比較不能なときは @lemma:FunH より従う．
    比較可能だと仮定する． ある $k in W$ について $epsilon_i paren.t brak(k) subset.eq epsilon_j$ と仮定する．
    $EA$ の内部で作業する．
    $i prec k$ より $Dia(T) solovay_k$.
    また $FunH_(epsilon_j)$ より $FunH_brak(i, k)$, 従って $Box(T) not solovay_k$ ↯.
  2. $solovay_i$ の定義から従う．
  3. @lemma:FunH の 3. と可証性条件より $EA proves Box(T)(FunH_i -> solovay_i or or.big_(j succ i) solovay_j)$.
    また $Sigma_1$-完全性より
    #footnote[唯一 $exists Pi^"b"_1$-完全性を使用している箇所．
      exponential の全域性が示せない理論で $exists Pi^"b"_1$-完全性が成立するかは未解決 @BeklemishevVisser2006, @BerarducciVerbrugge1993．
      なのでここではベース理論を $EA$ とした．]
    $EA proves FunH_i -> Box(T) FunH_i$.
    従って再び可証性条件より $EA proves FunH_i -> Box(T)(solovay_i or or.big_(j succ i) solovay_j)$.
    @lemma:FunH の 2. より $EA proves FunH_i -> Box(T)(or.big_(j succ i) solovay_j)$.
    よって $EA proves solovay_i -> Box(T)(or.big_(j succ i) solovay_j).$
  4. @lemma:FunH の 3. より従う．
]