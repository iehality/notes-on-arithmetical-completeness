#import "@preview/ctheorems:1.1.3": *
#import "@preview/codelst:2.0.2": sourcecode

#let lightlightgray = luma(81.18%)
#let lightgray = luma(160)
#let lavender = rgb("#9191ff")
#let lavender2 = rgb("#7b7bff")

#let project(
    title: "",
    authors: (),
    date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
    repo: "",
    license: "CC BY 4.0",
    body) = {
  set document(author: authors, title: title)

  set page(numbering: "1", number-align: center)

  set heading(numbering: "1.1")

  set text(size: 8pt, font: "Shippori Mincho B1")

  show math.equation: set text(font: ("New Computer Modern Math", "Shippori Mincho B1"))

  show raw: set text(size: 7pt, font: ("JuliaMono", "Noto Sans JP"))

  show raw.where(block: false): box.with(
    inset: (x: 0pt, y: 0pt),
    outset: (y: 3pt),
    radius: 1pt,
  )
  
  show raw.where(block: true): block.with(
    inset: 0pt,
    radius: 1pt,
  )

  show link: set text(weight: "bold", fill: lavender2)

  grid(
    columns: (auto, 1fr, auto),
    align: (left + horizon, center + bottom, right + top),
    rect(stroke: none, width: 220pt)[
      #block(text(weight: 700, 1.75em, title))
      #pad(
        top: .5em,
        x: 1em,
        grid(
          gutter: .6em,
          ..authors.map(author => text(strong(author))),
        )
      )
    ],
    stack(),
    rect(
      width: 65pt,
      fill: lightlightgray,
      stroke: none,
      inset: 15pt,
      text(
        fill: white,
        size: 6pt,        
        align(center)[
          #link(repo, [repository])
          #text(size: 8pt)[$ \* \* \* \*  $]
          #strong(license)
          #date.at(0)/#date.at(1)/#date.at(2)
        ]
      )
    ),
  )

  set par(justify: true)

  show: thmrules.with(qed-symbol: [#text(fill: lightgray)[❏]])

  body

  bibliography("references.bib")
}

#let sqthmbox(
    name,
    title,
    color: lightlightgray,
    color2: lightgray,
    dash: "solid",
    base: "heading") = thmbox(
  name,
  title,
  stroke: color,
  base: base,
  titlefmt: body => [
    #text(font: "Shippori Antique B1", size: 6.5pt, fill: color2)[#body]
  ],
  namefmt: name => [
    #text(font: "Shippori Antique B1", size: 6.5pt, fill: color2)[(#name)]
  ],
  separator: [
    #v(.1em)
  ],
)

#let barthmbox(
    name,
    title,
    color: lightlightgray,
    color2: lightgray,
    dash: "solid") = thmbox(
  name,
  title,
  stroke: (left: (thickness: 1pt, paint: color, dash: dash),),
  inset: (left: 12pt, top: 5pt, bottom: 8pt),
  radius: 0pt,
  titlefmt: body => [
    #text(font: "Shippori Antique B1", size: 6.5pt, fill: color2)[#body]
  ],
  namefmt: name => [
    #text(font: "Shippori Antique B1", size: 6.5pt, fill: color2)[(#name)]
  ],
  separator: [
    #v(.1em)
  ],
)

#let lemma = sqthmbox("lemma", "補題")

#let theorem = sqthmbox("theorem", "定理")

#let fact = sqthmbox("fact", "Fact")

#let corollary = sqthmbox("corollary", "系", base: "theorem", color: black, color2: black,)

#let definition = barthmbox("definition", "定義")

#let notation = barthmbox("notation", "記法", color: lavender, color2: lavender2, dash: "dotted")

#let remark = barthmbox("remark", "注意", color: lavender, color2: lavender2, dash: "dotted")

#let example = barthmbox("example", "例", color: lavender, color2: lavender2, dash: "dotted")

#let proof = thmproof(
  "proof",
  "Proof.",
  titlefmt: body => [
    #text(font: "Shippori Antique B1", size: 6.5pt, fill: lightgray)[#body]
  ],
  separator: [
    #v(.1em)
  ],
  )

#let struct(body) = {
  block(
    width: 100%,
    stroke: (left: (thickness: 1pt, paint: luma(230))),
    inset: (left: 12pt, top: 5pt, bottom: 8pt))[#body]
  }

#let code = sourcecode.with(
  numbers-start: 40,
  gutter: 1em,
  frame: block.with(
    radius: 0pt,
    fill: luma(250),
    stroke: (left: 1pt + luma(20)),
    inset: (x: 1.5em, y: 1em),
  ),
)

#let dand = $⩕$
#let dor = $⩖$

#let brak(..args) = {
  let a = args.pos().join(", ")
  $lr(angle.l #a angle.r)$
  }

#let doubleQuote(..args) = {
  let a = args.pos().join(", ")
  $lr(quote.l.double #a quote.r.double)$
  }

#let size(x) = $lr(| #x |)$

#let proves = $tack.r$
#let nproves = $tack.r.not$

#let nmodels = $cancel(models)$


#let Nat = $NN$
#let Rat = $QQ$
#let Real = $RR$

#let fal(x) = $forall #x space.nobreak.narrow$
#let exs(x) = $exists #x space.nobreak.narrow$

#let vec(x) = $arrow(#x)$
#let godel(x) = $lr(⌜ #x ⌝)$